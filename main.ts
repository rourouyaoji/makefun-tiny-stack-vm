// tiny-stack-vm: an interpreter for make.fun's tiny stack ISA (v1), written from the published spec.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode facts indexed by byte: [immediate length, values popped, values pushed]; null = not an opcode.
const META: ([number, number, number] | null)[] = new Array(256).fill(null);
const def = (b: number, imm: number, pops: number, pushes: number) => { META[b] = [imm, pops, pushes]; };
def(0x00, 0, 0, 0); def(0x01, 1, 0, 1); def(0x02, 4, 0, 1); // HALT, PUSH8, PUSH32
def(0x03, 0, 1, 0); def(0x04, 0, 1, 2); def(0x05, 0, 2, 2); def(0x06, 0, 2, 3); def(0x07, 0, 3, 3); // POP DUP SWAP OVER ROT
for (let b = 0x10; b <= 0x22; b++) if (b !== 0x1f) def(b, 0, (b === 0x17 || b === 0x1b) ? 1 : 2, 1); // arithmetic & compares
def(0x30, 2, 0, 0); def(0x31, 2, 1, 0); def(0x32, 2, 1, 0); def(0x33, 2, 0, 0); def(0x34, 0, 0, 0); // JMP JZ JNZ CALL RET
def(0x40, 0, 1, 1); def(0x41, 0, 2, 0); // LOAD, STORE
def(0x50, 0, 1, 0); def(0x51, 0, 1, 0); def(0x52, 0, 0, 1); def(0x53, 0, 1, 0); // PRINT PUTC IN EXIT

const STACK_CAP = 256, CALL_CAP = 64, MEM_WORDS = 256, STEP_CAP = 1_000_000, OUT_CAP = 65_536;

// Runs one program to its end; returns [emitted bytes, exit code].
function execute(prog: Uint8Array, input: Uint8Array): [Uint8Array, number] {
  const stack = new Int32Array(STACK_CAP), calls = new Int32Array(CALL_CAP), mem = new Int32Array(MEM_WORDS);
  const emitted = new Uint8Array(OUT_CAP);
  let sp = 0, csp = 0, pc = 0, steps = 0, olen = 0, inPos = 0;
  const finish = (code: number): [Uint8Array, number] => [emitted.slice(0, olen), code];

  for (;;) {
    // Per-step gate, in the ISA's order: steps, pc range, known opcode, immediate fits.
    if (steps >= STEP_CAP) return finish(10);
    if (pc < 0 || pc >= prog.length) return finish(9);
    const op = prog[pc], meta = META[op];
    if (meta === null) return finish(5);
    const [immLen, pops, pushes] = meta;
    if (pc + immLen >= prog.length) return finish(9);
    steps++;
    // Stack discipline precedes the instruction's own traps and effects.
    if (sp < pops) return finish(2);
    if (sp - pops + pushes > STACK_CAP) return finish(3);
    const after = pc + 1 + immLen; // next instruction's address
    // Immediates are read from the instruction's own bytes, before pc moves.
    const immByte = immLen >= 1 ? prog[pc + 1] : 0;
    const immSigned = immLen >= 2 ? ((prog[pc + 1] | (prog[pc + 2] << 8)) << 16) >> 16 : 0;
    const immRaw = immLen >= 2 ? prog[pc + 1] | (prog[pc + 2] << 8) : 0;
    const immQuad = immLen >= 4 ? prog[pc + 1] | (prog[pc + 2] << 8) | (prog[pc + 3] << 16) | (prog[pc + 4] << 24) : 0;
    pc = after;

    if (op === 0x00) return finish(0); // HALT
    if (op === 0x01) { stack[sp++] = (immByte << 24) >> 24; continue; } // PUSH8, sign-extended
    if (op === 0x02) { stack[sp++] = immQuad; continue; } // PUSH32, little-endian
    if (op === 0x03) { sp--; continue; } // POP
    if (op === 0x04) { stack[sp] = stack[sp - 1]; sp++; continue; } // DUP
    if (op === 0x05) { const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; continue; } // SWAP
    if (op === 0x06) { stack[sp] = stack[sp - 2]; sp++; continue; } // OVER
    if (op === 0x07) { const a = stack[sp - 3]; stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a; continue; } // ROT
    if (op === 0x17) { stack[sp - 1] = (-stack[sp - 1]) | 0; continue; } // NEG (wraps)
    if (op === 0x1b) { stack[sp - 1] = ~stack[sp - 1]; continue; } // NOT

    if (op >= 0x10 && op <= 0x22) { // binary operations: b is the top of stack, a below it
      const b = stack[sp - 1], a = stack[sp - 2];
      let r: number;
      switch (op) {
        case 0x10: r = (a + b) | 0; break;
        case 0x11: r = (a - b) | 0; break;
        case 0x12: r = Math.imul(a, b); break; // low 32 bits of the exact product
        case 0x13: if (b === 0) return finish(4); r = (a === -2147483648 && b === -1) ? a : Math.trunc(a / b) | 0; break;
        case 0x14: if (b === 0) return finish(4); r = b === -1 ? 0 : (a % b) | 0; break;
        case 0x15: if (b === 0) return finish(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
        case 0x16: if (b === 0) return finish(4); r = ((a >>> 0) % (b >>> 0)) | 0; break;
        case 0x18: r = a & b; break;
        case 0x19: r = a | b; break;
        case 0x1a: r = a ^ b; break;
        case 0x1c: r = a << (b & 31); break; // shift counts: low 5 bits only
        case 0x1d: r = a >> (b & 31); break;
        case 0x1e: r = (a >>> (b & 31)) | 0; break;
        case 0x20: r = a === b ? 1 : 0; break;
        case 0x21: r = a < b ? 1 : 0; break;
        default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // 0x22 LTU
      }
      stack[sp - 2] = r; sp--;
      continue;
    }

    if (op === 0x30 || op === 0x31 || op === 0x32) { // jumps: offset relative to the next instruction
      let go = op === 0x30;
      if (!go) { const v = stack[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
      if (go) pc = after + immSigned;
      continue;
    }
    if (op === 0x33) { // CALL: the immediate is an absolute address
      if (csp >= CALL_CAP) return finish(7);
      calls[csp++] = after; pc = immRaw;
      continue;
    }
    if (op === 0x34) { if (csp === 0) return finish(8); pc = calls[--csp]; continue; } // RET
    if (op === 0x40) { // LOAD
      const addr = stack[sp - 1];
      if (addr < 0 || addr >= MEM_WORDS) return finish(6);
      stack[sp - 1] = mem[addr];
      continue;
    }
    if (op === 0x41) { // STORE: value below, address on top
      const addr = stack[sp - 1], v = stack[sp - 2];
      if (addr < 0 || addr >= MEM_WORDS) return finish(6);
      mem[addr] = v; sp -= 2;
      continue;
    }
    if (op === 0x50) { // PRINT: decimal ASCII, all of it or none of it
      const text = String(stack[sp - 1]);
      if (olen + text.length > OUT_CAP) return finish(11);
      sp--;
      for (let i = 0; i < text.length; i++) emitted[olen++] = text.charCodeAt(i);
      continue;
    }
    if (op === 0x51) { if (olen + 1 > OUT_CAP) return finish(11); emitted[olen++] = stack[--sp] & 255; continue; } // PUTC
    if (op === 0x52) { stack[sp++] = inPos < input.length ? input[inPos++] : -1; continue; } // IN: -1 at/past end
    return finish(stack[--sp] & 255); // EXIT (0x53): only the low byte counts
  }
}

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(inputDir).sort()) {
  const prog = readFileSync(join(inputDir, id, 'program.bin'));
  let input: Uint8Array = new Uint8Array(0);
  try { input = readFileSync(join(inputDir, id, 'input.bin')); } catch { /* an instance may carry no input */ }
  const [bytes, code] = execute(prog, input);
  mkdirSync(join(outputDir, id), { recursive: true });
  writeFileSync(join(outputDir, id, 'stdout.bin'), bytes);
  writeFileSync(join(outputDir, id, 'exit.txt'), `${code}\n`);
}
