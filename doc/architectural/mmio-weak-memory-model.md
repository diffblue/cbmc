# A weak-memory model for memory-mapped I/O

## Motivation

Device drivers interact with hardware through **memory-mapped I/O (MMIO)**:
loads and stores to special addresses that are wired to device registers
rather than to RAM. Two properties make these accesses fundamentally different
from ordinary memory, and both are sources of real driver bugs:

1. **The device is a concurrent agent with side effects.** A load can observe a
   value the program never wrote (the device updated the register), and reading
   some registers *changes* them (e.g. reading a status register clears it, or
   pops a FIFO). A store is an *action* (it tells the device to do something),
   not just a state update that can be dropped if no later load observes it.

2. **The ordering rules are governed by the memory-type attributes**, not by
   the ordinary-memory model. On ARM, device memory is
   `Device-[n]G[n]R[n]E`; on x86 it is `UC` (uncacheable, strongly ordered) or
   `WC` (write-combining). These attributes decompose into three orthogonal
   questions:

   | Attribute | Question | Bug class it governs |
   |-----------|----------|----------------------|
   | **G / nG** (Gathering)   | may adjacent accesses be merged/split? | a 32-bit register write split into bytes, or two writes coalesced, when the device requires distinct accesses |
   | **R / nR** (Reordering)  | may accesses be reordered w.r.t. each other and w.r.t. normal memory (up to a barrier)? | missing `DMB`/`DSB`/`mb()` between two register writes, or between a register write and a normal-memory flag |
   | **E / nE** (Early ack)   | may a write "complete" before reaching the endpoint? | a completion barrier (`DSB`) that assumes the write has landed |

   The stronger types (`nGnRnE`, x86 `UC`) forbid gathering and reordering; the
   weaker ones (`GRE`, x86 `WC`) permit both, bounded by explicit barriers.
   Note this is *not* the ordinary-memory store-buffer (TSO/PSO) model — device
   memory is deliberately mapped to *suppress* normal caching/buffering and get
   ordered, side-effecting accesses.

The goal of this work is to let CBMC find real device-driver bugs by modelling
these two properties. We target **bug-finding**, so the guiding principle is
**sound over-approximation**: havoc what the device controls, and *allow* every
architecturally-permitted reordering so that missing-barrier bugs surface.

## What CBMC already provides

Much of the "device environment" already exists; the ordering part is where the
new work lies.

* **`goto-instrument --nondet-volatile`** (`nondet_volatile.cpp`) replaces every
  read of a `volatile`-qualified lvalue with a fresh non-deterministic value. It
  supports per-variable scoping (`--nondet-volatile-variable`) and read *models*
  (`--nondet-volatile-model <var>:<fn>`, a `T fn(void)` callback). It also (see
  Phase 1 below) preserves volatile *writes* as observable side effects and
  supports a write *model* (`--nondet-volatile-write-model <var>:<fn>`, a
  `void fn(T)` callback). This is the full device-environment model.
* **The `__CPROVER_mm_io_r`/`__CPROVER_mm_io_w` callback model**
  (`goto-programs/mm_io.cpp`) rewrites pointer-dereference reads/writes into
  calls to user-supplied callbacks, and the `--mmio-region <addr>:<size>`
  facility models declared regions as byte arrays. These require the user to
  supply callbacks / region addresses.
* **`goto-instrument --mm tso|pso|rmo|power`** (`wmm/`) is the ordinary-memory
  weak-memory engine: it builds an event graph, inserts per-variable store
  buffers (`shared_bufferst`), and understands fences (`wmm/fence.cpp`,
  `__sync_synchronize`, atomics). This is the machinery the MMIO *ordering*
  model should reuse — parameterised per region by device-memory type rather
  than globally.
* **Removed dead code:** `goto-instrument/mmio.cpp` used to contain a large
  `#if 0` block sketching a 2-entry store buffer for MMIO. It was a stale
  (~2011) prototype of the weak-memory store buffer, written against an outdated
  `shared_bufferst` API, and conceptually mislabelled (store buffering is a
  property of the *weak* device types, not MMIO in general). It has been
  **removed**; its idea survives, correctly, as Phase 2 below (write-combining
  memory via `wmm/`). `goto-instrument --mmio` is the entry point for the MMIO
  memory model: it applies the weakest device-memory model (sound for any
  mapping) with no further configuration, and is where the ordering model lives.

## Phased design

### Phase 1 — the device environment (this is the tractable, high-value core)

Model the device as an external agent, independent of ordering:

* **Reads → non-deterministic.** Already provided by `--nondet-volatile`
  (havoc) and its `--nondet-volatile-model` callback. Catches stale-read,
  missing-`volatile`, and polling-loop bugs (`while(*status == 0);` can now
  make progress because the device may set the flag).
* **Writes → observable side effects that are never eliminated.** A store to a
  device register must survive slicing/optimisation even when its value is
  never read back (which, under non-deterministic reads, is always). This is
  implemented: each write to a volatile lvalue that is modelled as a device
  emits an `OUTPUT` of the written value (so the store is not sliced away and
  appears in counterexample traces), and may instead be routed to a write
  *model* (`--nondet-volatile-write-model <var>:<fn>`, a `void fn(T)` callback)
  so a device model can assert on written values — the write-side analogue of
  `--nondet-volatile-model`. The zero-initialisation of globals is not treated
  as a device write.

Phase 1 is implemented for `volatile`-qualified regions; the read side
(`--nondet-volatile` and friends) predated this work, the write side was added
on top.

Region identification in Phase 1 is by `volatile` qualification (the C-level
signal drivers already use), with `--mmio-region` addresses as an alternative
where available. No ordering machinery is required.

### Phase 2 — ordering and the weak device types

This is the model reached by `goto-instrument --mmio`, the single sound default:
it applies the weakest device-memory model (weak ordering, gather and early
acknowledgement) to all volatile accesses, which over-approximates any real
mapping, so no flag combination has to be chosen. The individual options below
refine it when precision is wanted.

**Implemented (first increment):** `goto-instrument --mmio-weak` models weakly
ordered device memory as *posted writes*. A write to a register that has a
write model (`--nondet-volatile-write-model`) is non-deterministically either
committed immediately (the model is called at the write) or posted — deferred,
with the model call delivered at the next barrier or at the end of the
function. A barrier is a full fence or a call to `__sync_synchronize`. Because a
later write to a different register can be committed while an earlier write is
still posted, the device (the write model, acting as observer) may see the two
writes out of order, exposing missing-barrier bugs; a barrier between them
restores program order. Writes to a *single* register are observed in program
order (the posted writes form a per-register FIFO), while writes to *different*
registers may be reordered. The FIFO depth is set by `--mmio-weak-depth <n>`
(default 1): up to `n` writes to a register can be outstanding, so a write may
be delayed past that many writes to other registers; a deeper buffer exhibits
reorderings a shallower one cannot (e.g. delaying a write past a subsequent
write to the same register). The bound is not a hidden source of unsoundness: if
a write burst to a single register exceeds the buffer depth, the instrumentation
asserts the overflow ("MMIO write burst exceeds the modelled reorder depth"), so
the situation is reported (with a location) as a property violation and the user
can raise `--mmio-weak-depth`, rather than silently under-approximating. The
posted-write buffers have static lifetime, so a
write posted in one function can be delayed past the function's return and
observed later in the program, until a barrier or the end of the program; this
catches missing-barrier bugs that span function boundaries.

Per-register memory types are selected with `--mmio-weak-variable <register>`
(mark a specific register weak, leaving the rest strongly ordered), while
`--mmio-weak` marks every write-modelled register weak. A strongly-ordered
register's writes are observed in program order (ARM Device-nGnRnE, x86
uncacheable); a weakly-ordered register's writes are posted (ARM Device-GRE, x86
write-combining).

`--mmio-gather` additionally models the gathering attribute (write combining): a
write to a weakly-ordered register may be merged into the most recent
not-yet-observed write to the same register, so the device observes only the
merged value and an intermediate write may be lost.

The remaining design, of which the above is the first slice:

Tag each MMIO region with a memory type and reuse the `--mm` event-graph +
fence engine, parameterised per region instead of globally:

* **Strongly ordered (`nGnRnE`, x86 `UC`):** preserve program order among the
  region's accesses; treat them as ordering points; no buffer.
* **Write-combining / weak device (`GRE`, x86 `WC`):** permit write reordering
  and gathering up to a barrier — modelled by a store/merge buffer via
  `wmm/shared_buffers`, gated by the existing fence handling. *This is the
  correct home for the `#if 0` idea.*
* Barriers (`DMB`/`DSB`, `__sync_synchronize`, atomic fences) flush/​order,
  reusing the `--mm` fence model, giving MMIO↔normal-memory ordering.

Catches missing-barrier bugs between MMIO writes and between MMIO and ordinary
memory.

### Phase 3 — refinements

Gathering (`G`) is modelled by `--mmio-gather`, and early acknowledgement (`E`)
by `--mmio-early-ack` (see below). The remaining refinement is selectable
per-architecture profiles (ARM device types, x86 UC/WC) that bundle these
attributes into named memory types.

Under `--mmio-early-ack` a write's *completion* is separated from its *ordering*.
A lightweight fence (ARM `DMB`) is an ordering barrier: it bumps a global barrier
generation but does not flush, so posted writes remain in flight across it.
Each posted write is tagged with the generation it was issued in, and a write is
only observed once it is in the globally-oldest outstanding generation -- so
writes separated by a `DMB` are observed in order, while a `DMB` alone does not
guarantee a write has landed. A full fence or `__sync_synchronize` (ARM `DSB`)
is a completion barrier that flushes all posted writes. This gives the three-way
distinction: no barrier reorders freely; a `DMB` orders but does not complete; a
`DSB` orders and completes.

The barrier kind is taken from the source where possible. `remove_asm` lowers
inline-assembly barriers to fences, and distinguishes the ARM ordering barrier
`dmb` (marked ordering-only) from the completion barrier `dsb`; Power `lwsync`
(ordering) and `sync` (completion) are likewise distinguished by their fence
flags. So a driver that uses `asm volatile("dmb ...")` / `asm volatile("dsb
...")` — or the accessor macros that expand to them — gets the right
ordering-vs-completion semantics under `--mmio-early-ack` without any extra
annotation. The one memory attribute not derivable from the access site is the
region's memory *type* (weak/strong, gather), which is fixed by how the region
was mapped (e.g. `ioremap` vs `ioremap_wc`) rather than by the access. Because
that mapping is not in the analysed program, the type is supplied per region by
address: `--mmio-region <addr>:<size>[:<type>]` declares a region (backed by a
precise byte-array object) and its type -- `strong` (the default; modelled
precisely) or `weak` (reads return a non-deterministic value, soundly
over-approximating reordering/staleness). Address-based declaration recovers the
per-region type without a points-to analysis; a harness that stubs `ioremap`
already knows the address and can declare the region, and a future `ioremap`
library model could emit the declaration automatically.

## Soundness stance

For bug-finding we prefer over-approximation: non-deterministic reads soundly
model any device response, and (in Phase 2) allowing all permitted reorderings
ensures ordering bugs are not masked. Exhaustive *proof* of ordering-correct
drivers is a non-goal of the initial phases.
