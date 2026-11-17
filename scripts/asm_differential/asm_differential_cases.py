#!/usr/bin/env python3
"""Test cases for asm_differential.py.

Each case is one inline assembly statement, with the C variables it reads and
writes. The harness compiles and runs it on hardware (or an emulator) to
discover the expected results, then emits a CBMC regression test that pins
them. A case must therefore be deterministic: no reads of uninitialised
storage, timers, or I/O.
"""

from dataclasses import dataclass, field
from typing import Callable, List, Optional, Tuple


@dataclass
class Case:
    name: str
    statement: str
    # (C type, name, array length or None) for each variable, in io order
    variables: List[Tuple[str, str, Optional[int]]]
    # explicit input vectors (each a list of values, in io order)
    inputs: List[List[int]] = field(default_factory=list)
    # number of input vectors (explicit plus random)
    vectors: int = 8
    prologue: str = ''
    # optionally adjust a random vector so the case stays deterministic
    constrain: Optional[Callable[[List[int]], List[int]]] = None


U64 = 'unsigned long'
U32 = 'unsigned int'

X86_64 = [
    Case('x86 lock-or sets a bit (atomic_set_long)',
         '__asm__ __volatile__("lock; orq %1,%0" : "+m"(m) : "ir"(v) : "cc");',
         [(U64, 'm', None), (U64, 'v', None)]),
    Case('x86 lock-and clears bits (atomic_clear_long)',
         '__asm__ __volatile__("lock; andq %1,%0" : "+m"(m) : "ir"(v) : "cc");',
         [(U64, 'm', None), (U64, 'v', None)]),
    Case('x86 lock-add (atomic_add_long)',
         '__asm__ __volatile__("lock; addq %1,%0" : "+m"(m) : "ir"(v) : "cc");',
         [(U64, 'm', None), (U64, 'v', None)]),
    Case('x86 lock-xadd returns the previous value (atomic_fetchadd)',
         '__asm__ __volatile__("lock; xaddl %0,%1" : "+r"(v), "+m"(m) : : '
         '"cc");',
         [(U32, 'v', None), (U32, 'm', None)]),
    Case('x86 lock-bts sets a bit and reports its old value',
         '__asm__ __volatile__("lock; btsl %2,%0" : "+m"(m), "=@ccc"(c) : '
         '"Ir"(n) : "cc");',
         [(U32, 'm', None), (U32, 'c', None), (U32, 'n', None)],
         constrain=lambda v: [v[0], v[1], v[2] & 31]),
    Case('x86 bsr finds the highest set bit',
         '__asm__("bsrq %1,%0" : "=r"(r) : "rm"(v));',
         [(U64, 'r', None), (U64, 'v', None)],
         inputs=[[0, 1], [0, 0x8000000000000000], [0, 0x1234]],
         constrain=lambda v: [v[0], v[1] | 1]),
    Case('x86 add sets the carry flag',
         '__asm__("addl %2,%0; setc %b1" : "+r"(a), "+q"(c) : "r"(b) : "cc");',
         [(U32, 'a', None), (U32, 'c', None), (U32, 'b', None)]),
    Case('x86 shld-free shift: shr by cl',
         '__asm__("shrq %%cl,%0" : "+r"(a) : "c"(n) : "cc");',
         [(U64, 'a', None), (U64, 'n', None)],
         constrain=lambda v: [v[0], v[1] & 63]),
    Case('x86 bswap reverses byte order',
         '__asm__("bswapq %0" : "+r"(a));',
         [(U64, 'a', None)]),
    Case('x86 cmpxchg exchanges on a match (atomic_cmpset)',
         '__asm__ __volatile__("lock; cmpxchgl %3,%1" : "=@ccz"(ok), "+m"(m), '
         '"+a"(expected) : "r"(desired) : "cc");',
         [(U32, 'ok', None), (U32, 'm', None), (U32, 'expected', None),
          (U32, 'desired', None)]),
    Case('x86 xchg swaps a register and memory',
         '__asm__ __volatile__("xchgl %0,%1" : "+r"(r), "+m"(m));',
         [(U32, 'r', None), (U32, 'm', None)]),
    Case('x86 and masks and sets the sign flag',
         '__asm__("andl %2,%0; sets %b1" : "+r"(a), "+q"(s) : "r"(b) : "cc");',
         [(U32, 'a', None), (U32, 's', None), (U32, 'b', None)]),
    Case('x86 memory operand with a struct field offset',
         '__asm__ __volatile__("orl %1,%0" : "+m"(s.hi) : "r"(v) : "cc");',
         [(U32, 'lo', None), (U32, 'hi', None), (U32, 'v', None)],
         prologue='struct { unsigned int lo, hi; } s = {(unsigned)io[0], '
                  '(unsigned)io[1]};',
         vectors=4),
]

AARCH64 = [
    Case('aarch64 ldxr/add/stxr set a bit (atomic_set llsc)',
         '__asm__ __volatile__(\n'
         '    "1: ldxr %w0, [%2]\\n"\n'
         '    "   orr  %w0, %w0, %w3\\n"\n'
         '    "   stxr %w1, %w0, [%2]\\n"\n'
         '    "   cbnz %w1, 1b\\n"\n'
         '    : "=&r"(tmp), "=&r"(res) : "r"(&m), "r"(v) : "memory");',
         [(U32, 'm', None), (U32, 'v', None), (U32, 'tmp', None),
          (U32, 'res', None)]),
    Case('aarch64 ldadd is an atomic add (LSE)',
         '__asm__ __volatile__("ldadd %w2, %w0, [%1]" : "=r"(old) : "r"(&m), '
         '"r"(v) : "memory");',
         [(U32, 'm', None), (U32, 'v', None), (U32, 'old', None)]),
    Case('aarch64 ldset ORs into memory and returns the old value (LSE)',
         '__asm__ __volatile__("ldset %2, %0, [%1]" : "=r"(old) : "r"(&m), '
         '"r"(v) : "memory");',
         [(U64, 'm', None), (U64, 'v', None), (U64, 'old', None)]),
    Case('aarch64 swp exchanges a register and memory (LSE)',
         '__asm__ __volatile__("swp %w2, %w0, [%1]" : "=r"(old) : "r"(&m), '
         '"r"(v) : "memory");',
         [(U32, 'm', None), (U32, 'v', None), (U32, 'old', None)]),
    Case('aarch64 cas compares and swaps (LSE)',
         '__asm__ __volatile__("cas %w0, %w2, [%1]" : "+r"(cmp) : '
         '"r"(&m), "r"(newv) : "memory");',
         [(U32, 'm', None), (U32, 'cmp', None), (U32, 'newv', None)],
         vectors=0),
    Case('aarch64 add then subtract',
         '__asm__("add %0, %1, %2\\n sub %0, %0, %3" : "=&r"(r) : "r"(a), '
         '"r"(b), "r"(c));',
         [(U64, 'r', None), (U64, 'a', None), (U64, 'b', None),
          (U64, 'c', None)]),
    Case('aarch64 and with a shifted register',
         '__asm__("and %0, %1, %2, lsl #4" : "=r"(r) : "r"(a), "r"(b));',
         [(U64, 'r', None), (U64, 'a', None), (U64, 'b', None)]),
    Case('aarch64 cmp and cset compute a predicate',
         '__asm__("cmp %1, %2\\n cset %0, hi" : "=r"(r) : "r"(a), "r"(b) : '
         '"cc");',
         [(U64, 'r', None), (U64, 'a', None), (U64, 'b', None)]),
    Case('aarch64 ldr and str move a word through memory',
         '__asm__ __volatile__("ldr %w0, [%1]\\n str %w0, [%2]" : "=&r"(t) : '
         '"r"(&a), "r"(&b) : "memory");',
         [(U32, 'a', None), (U32, 'b', None), (U32, 't', None)]),
    Case('aarch64 eor and orr combine bits',
         '__asm__("eor %0, %1, %2\\n orr %0, %0, %3" : "=&r"(r) : "r"(a), '
         '"r"(b), "r"(c));',
         [(U64, 'r', None), (U64, 'a', None), (U64, 'b', None),
          (U64, 'c', None)]),
    Case('aarch64 lsl and lsr shift',
         '__asm__("lsl %0, %1, %2\\n lsr %0, %0, %3" : "=&r"(r) : "r"(a), '
         '"r"(b), "r"(c));',
         [(U64, 'r', None), (U64, 'a', None), (U64, 'b', None),
          (U64, 'c', None)],
         constrain=lambda v: [v[0], v[1], v[2] & 63, v[3] & 63]),
    Case('aarch64 movz/movk build a constant',
         '__asm__("movz %0, #0x1234\\n movk %0, #0xabcd, lsl #16" : "=r"(r));',
         [(U64, 'r', None)], vectors=1),
    Case('aarch64 ldp loads two adjacent doublewords',
         '__asm__ __volatile__("ldp %0, %1, [%2]" : "=r"(a), "=r"(b) : '
         '"r"(m) : "memory");',
         [(U64, 'm', 2), (U64, 'a', None), (U64, 'b', None)]),
    Case('aarch64 stp stores two adjacent doublewords',
         '__asm__ __volatile__("stp %1, %2, [%0]" : : "r"(m), "r"(a), '
         '"r"(b) : "memory");',
         [(U64, 'm', 2), (U64, 'a', None), (U64, 'b', None)]),
    Case('aarch64 ldp of words with an offset',
         '__asm__ __volatile__("ldp %w0, %w1, [%2, #4]" : "=r"(a), "=r"(b) : '
         '"r"(m) : "memory");',
         [(U32, 'm', 3), (U32, 'a', None), (U32, 'b', None)]),
    Case('aarch64 ldpsw sign-extends two words',
         '__asm__ __volatile__("ldpsw %0, %1, [%2]" : "=r"(a), "=r"(b) : '
         '"r"(m) : "memory");',
         [(U32, 'm', 2), (U64, 'a', None), (U64, 'b', None)]),
    Case('aarch64 ldp into the base register',
         '__asm__ __volatile__("ldp %0, %1, [%0]" : "+r"(p), "=r"(b) : : '
         '"memory");',
         [(U64, 'm', 2), (U64, 'b', None)], prologue='unsigned long *p = m;'),
]

# cas needs its compare value to sometimes match memory; supply fixed vectors
AARCH64[4].inputs = [
    [5, 5, 9], [5, 7, 9], [0, 0, 1], [0xdeadbeef, 0xdeadbeef, 1]]

ARM = [
    Case('arm ldrex/orr/strex set a bit (atomic set)',
         '__asm__ __volatile__(\n'
         '    "1: ldrex %0, [%2]\\n"\n'
         '    "   orr   %0, %0, %3\\n"\n'
         '    "   strex %1, %0, [%2]\\n"\n'
         '    "   teq   %1, #0\\n"\n'
         '    "   bne   1b\\n"\n'
         '    : "=&r"(tmp), "=&r"(res) : "r"(&m), "r"(v) : "cc", "memory");',
         [(U32, 'm', None), (U32, 'v', None), (U32, 'tmp', None),
          (U32, 'res', None)]),
    Case('arm add and subtract',
         '__asm__("add %0, %1, %2\\n sub %0, %0, %3" : "=&r"(r) : "r"(a), '
         '"r"(b), "r"(c));',
         [(U32, 'r', None), (U32, 'a', None), (U32, 'b', None),
          (U32, 'c', None)]),
    Case('arm adds/adc is a 64-bit add',
         '__asm__("adds %0, %2, %4\\n adc %1, %3, %5" : "=&r"(lo), "=&r"(hi) : '
         '"r"(alo), "r"(ahi), "r"(blo), "r"(bhi) : "cc");',
         [(U32, 'lo', None), (U32, 'hi', None), (U32, 'alo', None),
          (U32, 'ahi', None), (U32, 'blo', None), (U32, 'bhi', None)]),
    Case('arm and/orr/eor combine bits',
         '__asm__("and %0, %1, %2\\n orr %0, %0, %3\\n eor %0, %0, %4" : '
         '"=&r"(r) : "r"(a), "r"(b), "r"(c), "r"(d));',
         [(U32, 'r', None), (U32, 'a', None), (U32, 'b', None),
          (U32, 'c', None), (U32, 'd', None)]),
    Case('arm cmp and conditional move',
         '__asm__("cmp %1, %2\\n movhi %0, #1\\n movls %0, #0" : "=r"(r) : '
         '"r"(a), "r"(b) : "cc");',
         [(U32, 'r', None), (U32, 'a', None), (U32, 'b', None)]),
    Case('arm ldr and str move a word',
         '__asm__ __volatile__("ldr %0, [%1]\\n str %0, [%2]" : "=&r"(t) : '
         '"r"(&a), "r"(&b) : "memory");',
         [(U32, 'a', None), (U32, 'b', None), (U32, 't', None)]),
    Case('arm lsl/lsr shift',
         '__asm__("lsl %0, %1, %2\\n lsr %0, %0, %3" : "=&r"(r) : "r"(a), '
         '"r"(b), "r"(c));',
         [(U32, 'r', None), (U32, 'a', None), (U32, 'b', None),
          (U32, 'c', None)],
         constrain=lambda v: [v[0], v[1], v[2] & 31, v[3] & 31]),
    Case('arm bic clears bits',
         '__asm__("bic %0, %1, %2" : "=r"(r) : "r"(a), "r"(b));',
         [(U32, 'r', None), (U32, 'a', None), (U32, 'b', None)]),
    Case('arm rsb reverse-subtracts',
         '__asm__("rsb %0, %1, %2" : "=r"(r) : "r"(a), "r"(b));',
         [(U32, 'r', None), (U32, 'a', None), (U32, 'b', None)]),
]

CASES = {'x86_64': X86_64, 'aarch64': AARCH64, 'arm': ARM}
