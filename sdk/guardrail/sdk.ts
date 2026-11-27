// Zero-dependency TypeScript SDK for Forge `guardrail` 64-byte binary frame kernel.
// Auto-generated from canonical schema by `scripts/forge_vibe.py`.
//
// Provides capability-separated live process clients using Node built-ins only:
//   - `GuardrailAdmin`: owns process lifecycle + `depositAndConfigure` (`op=1`)
//     and mints restricted `GuardrailAgent` capabilities.
//   - `GuardrailAgent`: exposes ONLY `spend` (`op=2`), `refund` (`op=3`), and
//     `query` (`op=4`) with hard ECMAScript `#private` encapsulation.

import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { once } from "node:events";
import * as path from "node:path";

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

export interface SpawnOptions {
  qemu?: string;
  dockerImage?: string;
  cmd?: string[];
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

function buildKernelArgv(binary: string, opts?: SpawnOptions): [string, string[]] {
  if (opts?.cmd && opts.cmd.length > 0) {
    return [opts.cmd[0], opts.cmd.slice(1)];
  }
  if (opts?.dockerImage) {
    const absBin = path.resolve(binary);
    return [
      "docker",
      [
        "run",
        "--rm",
        "-i",
        "-v",
        `${path.dirname(absBin)}:/work:ro`,
        opts.dockerImage,
        `/work/${path.basename(absBin)}`,
      ],
    ];
  }
  if (opts?.qemu) {
    return [opts.qemu, [binary]];
  }
  return [binary, []];
}

interface PendingRead {
  resolve: (frame: Uint8Array) => void;
  reject: (err: Error) => void;
}

class KernelPipe {
  #child: ChildProcessWithoutNullStreams;
  #buf: Buffer = Buffer.alloc(0);
  #waiter: PendingRead | null = null;
  #queue: Promise<void> = Promise.resolve();
  #closed = false;
  #exitPromise: Promise<number>;

  constructor(program: string, args: string[]) {
    this.#child = spawn(program, args, { stdio: ["pipe", "pipe", "pipe"] });
    this.#exitPromise = new Promise<number>((resolve, reject) => {
      this.#child.once("error", reject);
      this.#child.once("close", (code, sig) => {
        this.#closed = true;
        if (this.#waiter) {
          const w = this.#waiter;
          this.#waiter = null;
          w.reject(new Error(`kernel stdout closed prematurely (code=${code}, sig=${sig})`));
        }
        resolve(code ?? (sig ? 1 : 0));
      });
    });

    this.#child.stdout.on("data", (chunk: Buffer) => {
      this.#buf = this.#buf.length === 0 ? chunk : Buffer.concat([this.#buf, chunk]);
      if (this.#waiter && this.#buf.length >= FRAME_BYTES) {
        const frame = new Uint8Array(this.#buf.subarray(0, FRAME_BYTES));
        this.#buf = this.#buf.subarray(FRAME_BYTES);
        const w = this.#waiter;
        this.#waiter = null;
        w.resolve(frame);
      }
    });

    this.#child.stdout.on("end", () => {
      if (this.#waiter) {
        const w = this.#waiter;
        this.#waiter = null;
        w.reject(new Error(`kernel stdout EOF after ${this.#buf.length} of ${FRAME_BYTES} bytes`));
      }
    });
  }

  #readExact64(): Promise<Uint8Array> {
    if (this.#buf.length >= FRAME_BYTES) {
      const frame = new Uint8Array(this.#buf.subarray(0, FRAME_BYTES));
      this.#buf = this.#buf.subarray(FRAME_BYTES);
      return Promise.resolve(frame);
    }
    if (this.#closed) {
      return Promise.reject(new Error("guardrail kernel process is closed"));
    }
    return new Promise<Uint8Array>((resolve, reject) => {
      this.#waiter = { resolve, reject };
    });
  }

  sendFrame(req: RequestFrame): Promise<ResponseFrame> {
    const encoded = encodeRequestFrame(req);
    const run = async (): Promise<ResponseFrame> => {
      if (this.#closed) {
        throw new Error("guardrail kernel process is closed");
      }
      const readPromise = this.#readExact64();
      const ok = this.#child.stdin.write(encoded);
      if (!ok) {
        await once(this.#child.stdin, "drain");
      }
      const rawResp = await readPromise;
      return decodeResponseFrame(rawResp);
    };
    const next = this.#queue.then(run, run);
    this.#queue = next.then(
      () => undefined,
      () => undefined,
    );
    return next;
  }

  async close(): Promise<number> {
    await this.#queue;
    if (!this.#closed) {
      this.#child.stdin.end();
    }
    return this.#exitPromise;
  }
}

const AGENT_TOKEN = Symbol("GuardrailAgentToken");
const AGENT_ALLOWED_OPS = new Set<bigint>([OP_SPEND_REQUEST, OP_REFUND, OP_QUERY]);

export class GuardrailAgent {
  readonly agentId: bigint;
  #send: (req: RequestFrame) => Promise<ResponseFrame>;

  constructor(
    agentId: bigint,
    sendFn: (req: RequestFrame) => Promise<ResponseFrame>,
    token: symbol,
  ) {
    if (token !== AGENT_TOKEN) {
      throw new TypeError("GuardrailAgent must be minted via GuardrailAdmin.mintAgent()");
    }
    this.agentId = checkU64("agentId", agentId);
    this.#send = sendFn;
  }

  spend(destId: bigint, amount: bigint, nonce: bigint): Promise<ResponseFrame> {
    return this.#send(spendReq(this.agentId, destId, amount, nonce));
  }

  refund(txId: bigint, amount: bigint): Promise<ResponseFrame> {
    return this.#send(refundReq(txId, amount, this.agentId));
  }

  query(): Promise<ResponseFrame> {
    return this.#send(queryReq(this.agentId));
  }
}

export class GuardrailAdmin {
  #pipe: KernelPipe;

  private constructor(pipe: KernelPipe) {
    this.#pipe = pipe;
  }

  static spawn(binary: string, opts?: SpawnOptions): GuardrailAdmin {
    const [program, args] = buildKernelArgv(binary, opts);
    return new GuardrailAdmin(new KernelPipe(program, args));
  }

  depositAndConfigure(
    deposit: bigint,
    cap: bigint,
    allowlistMask: bigint,
    agentId = 0n,
  ): Promise<ResponseFrame> {
    return this.#pipe.sendFrame(budgetSetReq(deposit, cap, allowlistMask, agentId));
  }

  deposit_and_configure(
    deposit: bigint,
    cap: bigint,
    allowlistMask: bigint,
    agentId = 0n,
  ): Promise<ResponseFrame> {
    return this.depositAndConfigure(deposit, cap, allowlistMask, agentId);
  }

  query(agentId = 0n): Promise<ResponseFrame> {
    return this.#pipe.sendFrame(queryReq(agentId));
  }

  mintAgent(agentId: bigint): GuardrailAgent {
    const pipe = this.#pipe;
    const restrictedSend = (req: RequestFrame): Promise<ResponseFrame> => {
      if (!AGENT_ALLOWED_OPS.has(req.op)) {
        return Promise.reject(new Error(`GuardrailAgent is forbidden from invoking op=${req.op}`));
      }
      return pipe.sendFrame(req);
    };
    return new GuardrailAgent(agentId, restrictedSend, AGENT_TOKEN);
  }

  close(): Promise<number> {
    return this.#pipe.close();
  }
}
