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
  (`--nondet-volatile-model <var>:<fn>`, a `T fn(void)` callback). This is
  exactly the *read* half of the device-environment model. It does **not**
  touch volatile writes.
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
* **Dead code:** `goto-instrument/mmio.cpp` contains a large `#if 0` block that
  sketched a 2-entry store buffer for MMIO. It is a stale (~2011) prototype of
  the weak-memory store buffer, written against an outdated `shared_bufferst`
  API, and is conceptually mislabelled (store buffering is a property of the
  *weak* device types, not MMIO in general). It should be **deleted**: its idea
  survives, correctly, as Phase 2 below (write-combining memory via `wmm/`),
  not as a bespoke copy.

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
  the piece `--nondet-volatile` is missing, and the initial implementation
  target: preserve volatile writes as observable events, optionally routed to a
  write *model* (a `void fn(T)` callback) so the device model can assert on
  written values — the write-side analogue of `--nondet-volatile-model`.

Region identification in Phase 1 is by `volatile` qualification (the C-level
signal drivers already use), with `--mmio-region` addresses as an alternative
where available. No ordering machinery is required.

### Phase 2 — ordering and the weak device types

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

Precise gathering rules (`G`), early-write-acknowledgement (`E`) interaction
with completion barriers, and selectable per-architecture profiles (ARM device
types, x86 UC/WC).

## Soundness stance

For bug-finding we prefer over-approximation: non-deterministic reads soundly
model any device response, and (in Phase 2) allowing all permitted reorderings
ensures ordering bugs are not masked. Exhaustive *proof* of ordering-correct
drivers is a non-goal of the initial phases.
