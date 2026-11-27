// Zero-dependency TypeScript SDK for Forge `guardrail` 64-byte binary frame kernel.
// Auto-generated from canonical schema by `scripts/forge_vibe.py`.

export const FRAME_BYTES = 64;

export const OP_BUDGET_SET = 1n;
export const OP_SPEND_REQUEST = 2n;
export const OP_REFUND = 3n;
export const OP_QUERY = 4n;

export interface RequestFrame {
  op: bigint;
  agentId: bigint;
  arg2: bigint;
  amount: bigint;
  arg4: bigint;
  reserved5?: bigint;
  reserved6?: bigint;
  reserved7?: bigint;
}

export interface ResponseFrame {
  ok: bigint;
  code: bigint;
  deposits: bigint;
  balance: bigint;
  netSpent: bigint;
  refunds: bigint;
  lastNonce: bigint;
  lastTxId: bigint;
}

const U64_MAX = 0xFFFFFFFFFFFFFFFFn;

function checkU64(name: string, v: bigint): bigint {
  if (v < 0n || v > U64_MAX) {
    throw new RangeError(`${name} out of u64 range: ${v}`);
  }
  return v;
}

export function encodeRequestFrame(r: RequestFrame): Uint8Array {
  const buf = new Uint8Array(FRAME_BYTES);
  const dv = new DataView(buf.buffer);
  dv.setBigUint64(0, checkU64("op", r.op), true);
  dv.setBigUint64(8, checkU64("agentId", r.agentId), true);
  dv.setBigUint64(16, checkU64("arg2", r.arg2), true);
  dv.setBigUint64(24, checkU64("amount", r.amount), true);
  dv.setBigUint64(32, checkU64("arg4", r.arg4), true);
  dv.setBigUint64(40, checkU64("reserved5", r.reserved5 ?? 0n), true);
  dv.setBigUint64(48, checkU64("reserved6", r.reserved6 ?? 0n), true);
  dv.setBigUint64(56, checkU64("reserved7", r.reserved7 ?? 0n), true);
  return buf;
}

export function decodeRequestFrame(buf: Uint8Array): RequestFrame {
  if (buf.byteLength !== FRAME_BYTES) {
    throw new Error(`expected ${FRAME_BYTES} bytes, got ${buf.byteLength}`);
  }
  const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  return {
    op: dv.getBigUint64(0, true),
    agentId: dv.getBigUint64(8, true),
    arg2: dv.getBigUint64(16, true),
    amount: dv.getBigUint64(24, true),
    arg4: dv.getBigUint64(32, true),
    reserved5: dv.getBigUint64(40, true),
    reserved6: dv.getBigUint64(48, true),
    reserved7: dv.getBigUint64(56, true),
  };
}

export function encodeResponseFrame(r: ResponseFrame): Uint8Array {
  const buf = new Uint8Array(FRAME_BYTES);
  const dv = new DataView(buf.buffer);
  dv.setBigUint64(0, checkU64("ok", r.ok), true);
  dv.setBigUint64(8, checkU64("code", r.code), true);
  dv.setBigUint64(16, checkU64("deposits", r.deposits), true);
  dv.setBigUint64(24, checkU64("balance", r.balance), true);
  dv.setBigUint64(32, checkU64("netSpent", r.netSpent), true);
  dv.setBigUint64(40, checkU64("refunds", r.refunds), true);
  dv.setBigUint64(48, checkU64("lastNonce", r.lastNonce), true);
  dv.setBigUint64(56, checkU64("lastTxId", r.lastTxId), true);
  return buf;
}

export function decodeResponseFrame(buf: Uint8Array): ResponseFrame {
  if (buf.byteLength !== FRAME_BYTES) {
    throw new Error(`expected ${FRAME_BYTES} bytes, got ${buf.byteLength}`);
  }
  const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  return {
    ok: dv.getBigUint64(0, true),
    code: dv.getBigUint64(8, true),
    deposits: dv.getBigUint64(16, true),
    balance: dv.getBigUint64(24, true),
    netSpent: dv.getBigUint64(32, true),
    refunds: dv.getBigUint64(40, true),
    lastNonce: dv.getBigUint64(48, true),
    lastTxId: dv.getBigUint64(56, true),
  };
}

export const budgetSetReq = (deposit: bigint, cap: bigint, allowlistMask: bigint, agentId = 0n): RequestFrame => ({
  op: OP_BUDGET_SET, agentId, arg2: allowlistMask, amount: deposit, arg4: cap,
});

export const spendReq = (agentId: bigint, destId: bigint, amount: bigint, nonce: bigint): RequestFrame => ({
  op: OP_SPEND_REQUEST, agentId, arg2: destId, amount, arg4: nonce,
});

export const refundReq = (txId: bigint, amount: bigint, agentId = 0n): RequestFrame => ({
  op: OP_REFUND, agentId, arg2: 0n, amount, arg4: txId,
});

export const queryReq = (agentId = 0n): RequestFrame => ({
  op: OP_QUERY, agentId, arg2: 0n, amount: 0n, arg4: 0n,
});
