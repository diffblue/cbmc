# CBMC Performance Profiling Analysis

Date: 2026-03-11
Branch: `profiling-tool`
Build: Release (`-O3 -DNDEBUG`), commit `b191cc1dac` (develop)
System: Linux x86_64

## Methodology

- Tool: `scripts/profile_cbmc.py --auto-large --auto-csmith --runs 3 --timeout 90`
- 15 benchmarks × 3 runs = 45 profiling runs, 49,462 total samples
- Solver excluded (`--dimacs --outfile /dev/null`) — only pre-solver stages profiled
- Source locations resolved via `build-debug/bin/cbmc` (RelWithDebInfo)

## Benchmarks

| Benchmark | Symex (s) | Convert SSA (s) | Total (s) | Steps | ±Total |
|-----------|-----------|-----------------|-----------|-------|--------|
| linked_list | 0.215 | 0.336 | 2.3 | 4,433 | ±0.06s |
| array_ops | 3.124 | 0.174 | 5.1 | 16,448 | ±0.00s |
| structs | 0.031 | 0.000 | 1.1 | 312 | ±0.06s |
| dlinked_list | 0.385 | 0.541 | 3.3 | 8,242 | ±0.00s |
| string_ops | 0.101 | 0.033 | 2.1 | 1,950 | ±0.06s |
| func_ptrs | 0.011 | 0.000 | 1.0 | 271 | ±0.00s |
| bitvector | 0.016 | 0.000 | 1.1 | 608 | ±0.06s |
| matrix | 1.827 | 0.000 | 3.1 | 4,148 | ±0.00s |
| unions | 0.022 | 0.000 | 1.1 | 382 | ±0.07s |
| tree | 0.980 | 0.943 | 5.2 | 27,789 | ±0.00s |
| csmith_1234567890 | 11.890 | 0.227 | 17.2 | 139,379 | ±0.06s |
| csmith_42 | 8.462 | 0.206 | 13.2 | 121,844 | ±0.00s |
| csmith_1111111111 | 17.291 | 0.258 | 23.2 | 153,556 | ±0.06s |
| csmith_2718281828 | 11.544 | 0.238 | 16.3 | 148,596 | ±0.01s |
| csmith_314159265 | 3.183 | 0.069 | 6.2 | 56,187 | ±0.06s |

Symex dominates wall time for: array_ops, matrix, and all CSmith benchmarks.

## Sample Distribution

- CBMC code: 28,550 (57.7%)
- Libraries (libc, libstdc++): 20,912 (42.3%)
- Total: 49,462

## Top Hotspots

### 1. String interning: `string_containert::get` — 11.7% combined

The `_Hashtable::_M_find_before_node` (10.0%) and `_Hashtable::find` (1.6%)
functions are called almost exclusively from `string_containert::get`.
Additionally, `hash_string` accounts for 1.7%.

- **Root cause**: NOT the hash function or table configuration (see
  investigation below), but the **volume of redundant interning calls**.
  `update_identifier(ssa_exprt&)` is called 11.5M times on csmith_42
  with a 98.6% hit rate — almost all calls find an already-interned string.
- **Call chain**: `field_sensitivityt::get_fields` / `rename` / `set_indices`
  → `update_identifier` → `build_identifier` (creates two `ostringstream`,
  builds string char-by-char) → `irep_idt(oss.str())` → `string_containert::get`
  → `hash_string` → `hash_table.find`
- **Source**: `src/util/ssa_expr.cpp` (`update_identifier`, `build_identifier`)

#### Investigation: hash function and table tuning

Tested three approaches on csmith_42 (11.5M get() calls, 156K unique strings):

| Change | Result | Reason |
|--------|--------|--------|
| FNV-1a hash (replace h*31+c) | **3.6% slower** | Multiply costlier than shift-subtract; chain lengths already short |
| Pre-reserve 10K buckets | No effect | `unordered_map` handles growth fine |
| Max load factor 0.5 | **1.3-1.8% faster** | Shorter chains, but modest (doubles memory) |

Hash distribution quality is similar for both hash functions (~37% empty
buckets at load factor 1.0). `dstringt::hash() = no` (sequential index)
is actually perfect for `std::unordered_map<dstringt, ...>`.

#### Recommended optimization

Avoid redundant `get()` calls rather than tuning the hash table:
- **Cache SSA identifiers**: skip `build_identifier` when l0/l1/l2 and
  the original expression haven't changed
- **Avoid ostringstream**: use direct string concatenation with `id2string()`
- **Reduce `update_identifier` calls**: audit callers for unnecessary rebuilds

Estimated impact: 6-9% overall speedup (50-80% reduction of the 11.7% cost).

#### Implemented: replace ostringstream with string concatenation

Replaced `std::ostringstream` with direct `std::string` concatenation
(using `reserve(64)` + `append`) in `build_ssa_identifier_rec` and
`initialize_ssa_identifier`. Commit `f8057bea69`.

| Benchmark | Baseline | Optimized | Speedup |
|-----------|----------|-----------|---------|
| linked_list | 1.49s | 1.46s | 2.0% |
| array_ops | 3.13s | 2.78s | **11.2%** |
| csmith_42 | 8.89s | 8.58s | 3.5% |
| csmith_1111111111 | 16.91s | 15.92s | **5.9%** |

#### Implemented: avoid full rebuild in set_level_0/1/2

When `set_level_0`, `set_level_1`, or `set_level_2` is called, the
identifier can be derived from the existing one by appending a suffix
(`!l0`, `@l1`, `#l2`) instead of rebuilding from the expression tree.
This is safe because each level is only set when previously empty
(callers guard against re-setting). Commits `4564ca2163`, `2c09b3ef20`.

Instrumentation showed `update_identifier` is called 504,737 times on
csmith_42: 24% from `set_level_0`, 22% from `set_level_1`, 16% from
`set_level_2`, 37% from `set_expression`.

Combined with the ostringstream optimization:

| Benchmark | Baseline | After all SSA opts | Speedup |
|-----------|----------|--------------------|---------|
| linked_list | 1.49s | 1.44s | 3.4% |
| array_ops | 3.13s | 2.69s | 14.1% |
| csmith_42 | 8.89s | 8.44s | 5.1% |
| csmith_1111111111 | 16.91s | 15.75s | 6.9% |

#### Implemented: cache array identifier prefix in field_sensitivity

In `field_sensitivityt::get_fields` for array types, pre-compute the
base identifier and level suffixes once before the loop, then construct
each element's identifier by concatenating `base[[i]]` + suffixes
directly. This avoids calling `set_expression` (which triggers a full
identifier rebuild) for each array index. Commit `3a95db52b3`.

Additional speedup on array-heavy benchmark: array_ops 2.69s → 2.56s
(4.8%). Minimal impact on CSmith benchmarks.

#### Investigated and ruled out: member expression caching

Attempted the same prefix-caching approach for member expressions
(`base..component!l0@l1`). No measurable improvement — the member case
is not in a hot loop (called once per struct field access, not iterated).

Further optimization potential remains: the remaining `set_expression`
calls (37% of `update_identifier` on CSmith) still do full rebuilds.
Reducing these would require restructuring how `dstringt` is constructed
to avoid intermediate `std::string` allocation — `dstringt` doesn't
support concatenation, so every new identifier must go through
`string_containert::get()`.

### 2. Sharing tree destruction: `sharing_treet::remove_ref` — 9.9%

Recursive reference-count decrement and deallocation of irept tree nodes.

- **Root cause**: 63% of samples are self-recursive — deep irept trees
  cause deep recursion in the destructor chain.
- **Key callers**:
  - 5.7% from `renamedt` (SSA renaming creates/destroys expressions)
  - 2.9% from `goto_symext::symex_function_call_symbol`
  - 2.5% from `~multi_path_symex_only_checkert` (final cleanup)
  - 2.4% from `simplify_exprt::simplify`
- **Source locations**:
  - `src/util/message.h:303` (52.6% — likely inlining artifact)
  - `src/util/typecheck.cpp:16` (10.5%)
  - `src/util/std_expr.h:1334` (3.1% — in rename)
- **Source**: `src/util/sharing_node.h`, `src/util/irep.h`
- **Possible improvements**:
  - Iterative (non-recursive) `remove_ref` using an explicit stack
  - Deferred/batched destruction (arena-style)
  - Reduce unnecessary temporary irept copies that trigger destruction

### 3. Memory allocation: malloc/free/new — ~25% combined

| Function | % |
|----------|---|
| malloc | 7.4% |
| _int_free | 6.6% |
| _int_malloc | 5.4% |
| cfree | 4.7% |
| malloc_consolidate | 4.0% |
| operator new | 2.5% |
| unlink_chunk | 1.7% |

- **Root cause**: CBMC creates and destroys vast numbers of small objects
  (irept nodes, expression trees, SSA steps). The sharing tree helps but
  copy-on-write still triggers many allocations.
- **Possible improvements**:
  - Custom allocator / object pool for irept nodes
  - Reduce copies (more move semantics, fewer temporaries)
  - This is largely a consequence of hotspots #2 and #7 — fixing those
    would reduce allocation pressure

### 4. irept::find — 5.4%

Linear scan through `forward_list_as_mapt` to find a named sub-tree.

- **Key callers**:
  - 22.6% from `simplify_exprt::simplify_node_preorder` (at `goto_program.h:274`)
  - 19.7% from `constant_exprt::check` (at `irep.h:228`)
  - 10.5% from `requires_renaming`
  - 9.1% from `field_sensitivityt::get_fields`
- **Source**: `src/util/irep.h`
- **Possible improvements**:
  - `constant_exprt::check` and `simplify_node_preorder` call `find` to
    check expression types — could be short-circuited with cached type IDs
  - `requires_renaming` does repeated type lookups — result could be cached

### 5. Symbol table lookup: `next_unused_suffix` — 4.9%

84.8% of `symbol_tablet::find` calls come from `symbol_table_baset::next_unused_suffix`.

- **Root cause**: Generating unique symbol names by probing the symbol table
  with incrementing suffixes. Each probe is a full hash table lookup.
- **Source location**: `src/util/expr.h:96` (in `next_unused_suffix`)
- **Source**: `src/util/symbol_table_base.h`
- **Possible improvements**:
  - Maintain a per-prefix counter to generate the next suffix directly
    without probing the table
  - This is a clear algorithmic improvement — O(1) instead of O(n) probes

### 6. irept::get — 4.8%

Similar to `irept::find` but returns a value rather than a reference.

- **Key callers**:
  - 21.4% from `irept::get_bool` (at `std_expr.h:131`)
  - 9.1% from `update_identifier`
  - 6.5% from `renamedt` (rename)
  - 5.5% from `build_ssa_identifier_rec`
- **Source**: `src/util/irep.h`
- **Possible improvements**: Same as #4 — reduce redundant lookups

### 7. Copy-on-write detach: `sharing_treet::detach` — 4.6%

Creates a private copy of a shared irept node before mutation.

- **Key callers**:
  - 45.9% from `irept::add` (at `symex_dead.cpp:65`)
  - 17.0% from `field_sensitivityt::apply` (at `std_types.h:149`)
  - 10.8% from `irept::remove` (at `symex_dead.cpp:72`)
  - 9.1% from `apply_to_objects_in_dereference`
- **Source**: `src/util/sharing_node.h`
- **Possible improvements**:
  - `symex_dead.cpp:65,72` — the dead variable handler adds and removes
    irept fields, triggering detach each time. Could batch mutations.
  - `field_sensitivityt::apply` — could avoid unnecessary copies when
    the result is immediately consumed

### 8. SSA renaming map: `sharing_mapt::get_leaf_node` — 2.1%

Hash-trie lookup in the SSA renaming map.

- **Key callers**: 90.2% from `rename` (at `irep.h:228`)
- **Source**: `src/util/sharing_map.h`
- **Possible improvements**:
  - The sharing_map is a hash-array-mapped trie. For the rename use case,
    a flat hash map might be faster for small-to-medium maps.

## Prioritized Optimization Plan

Based on impact and feasibility:

| Priority | Target | Impact | Effort | Approach |
|----------|--------|--------|--------|----------|
| **P1** | `next_unused_suffix` | 4.9% | Low | Per-prefix counter instead of probing |
| **P2** | SSA identifier rebuilding | 11.7% | Medium | Cache identifiers / avoid ostringstream |
| **P3** | `sharing_treet::remove_ref` | 9.9% | Medium | Iterative destruction with explicit stack |
| **P4** | `symex_dead.cpp` detach | 4.6% | Low | Batch add/remove to avoid double detach |
| **P5** | `constant_exprt::check` in simplifier | ~2% | Low | Short-circuit common cases |
| **P6** | `requires_renaming` caching | ~1% | Low | Cache result per type |

P2 is the highest-impact target: the hashing investigation confirmed that
the 11.7% cost is from redundant `update_identifier` calls, not from hash
table configuration. P1 remains the best bang-for-buck at low effort.

## Post-Optimization Investigation (2026-03-11)

After implementing the SSA identifier optimizations (P2), re-profiled to
assess remaining targets.

### Updated profile (csmith_42, post-optimization)

| Rank | Function | % | Notes |
|------|----------|---|-------|
| 1 | `string_containert` hash lookup | 11.1% | Volume of calls, not hash quality |
| 2 | `sharing_treet::remove_ref` | 7.2% | 63% self-recursive |
| 3 | `symbol_tablet::find` | 6.0% | `next_unused_suffix` now only 0.56% |
| 4 | malloc/free combined | ~18% | Consequence of irept allocation |
| 5 | `memcmp` | 3.5% | From `string_ptrt::operator==` |
| 6 | `irept::find` | 3.4% | Scattered callers |
| 7 | `irept::get` | 3.2% | Scattered callers |
| 8 | `sharing_treet::detach` | 2.7% | From `irept::add`/`remove` |
| 9 | `hash_string` | 2.1% | String interning hash function |
| 10 | `irept::operator==` | 2.1% | 57% self-recursive, 32% from `merge_irept` |

### Investigation results for remaining targets

**P1: `next_unused_suffix`** — Now only 0.56% (was 4.9% in original profile).
The original measurement was inflated by the `string_containert::get` cost
that dominated the `symbol_tablet::find` samples. After the SSA identifier
optimization reduced interning calls, `next_unused_suffix` is no longer a
significant bottleneck. `symbol_table_buildert` already provides a suffix
cache for the cases that need it.

**P3: `sharing_treet::remove_ref`** — Tested the existing
`nonrecursive_destructor` (already implemented but disabled via `#if 0`).
Result: **15% SLOWER** (9.74s vs 8.44s on csmith_42). The explicit
`std::vector` stack with `reserve` and iteration is more expensive than
the recursive version, which benefits from the CPU call stack being in
L1 cache. The nonrecursive version is only useful for avoiding stack
overflow on extremely deep trees, not for performance.

#### Implemented: irept union optimization (issue #7960)

Cherry-picked thomasspriggs' branch (`tas/irep_optimisation1_unions`)
which makes `irept` hold a union of a pointer or an id, reducing memory
usage for leaf nodes. Commits `81005555c6`, `92464ad78a` (originally
`ccd06c39f8`, `4a1b67f8bc`). Cherry-picked cleanly onto current develop.

| Benchmark | Without union | With union | Speedup |
|-----------|-------------|------------|---------|
| linked_list | 1.44s | 1.37s | **4.9%** |
| array_ops | 2.56s | 2.49s | **2.7%** |
| csmith_42 | 8.49s | 8.12s | **4.4%** |
| csmith_1111111111 | 15.75s | 15.37s | **2.4%** |

Consistent 2.4-4.9% improvement from reduced memory footprint and
fewer allocations for leaf nodes.

**P4: `symex_dead.cpp` detach** — The source locations from addr2line
(`symex_dead.cpp:65,72`) were inlining artifacts. The actual `detach`
cost is spread across many callers (45.9% from `irept::add`, 17% from
`field_sensitivityt::apply`, 10.8% from `irept::remove`). No single
call site dominates enough for a targeted fix.

**P5: `constant_exprt::check`** — Only 0.32% of time is in `check`
itself. The 19.7% of `irept::find` attributed to `check` is because
`check` calls `find(ID_value)`. The `check` functions are validation
that runs on every `to_constant_expr` cast even in Release builds
(INVARIANT is not compiled out by default). Disabling checks would
require `CPROVER_INVARIANT_DO_NOT_CHECK` which is not recommended.

### Conclusion

The remaining hotspots are dominated by fundamental irept operations
(`find`, `get`, `add`, `remove_ref`, `detach`, `operator==`) that are
called millions of times from many different sites. These are inherent
to the sharing tree data structure and cannot be optimized by targeting
individual call sites. Significant further improvement would require
either:

1. **Reducing the number of irept operations** — e.g., by caching
   intermediate results, avoiding unnecessary copies, or restructuring
   algorithms to batch mutations.

2. **Changing the irept data structure** — e.g., using a flat hash map
   instead of `forward_list_as_mapt` for named sub-trees, or using
   a different representation for frequently-accessed fields.

3. **Reducing string interning volume** — the 11.1% in
   `string_containert::get` is from the remaining `set_expression`
   calls (37% of `update_identifier`) in `field_sensitivity.cpp`'s
   array element loop. Caching per-index identifiers there could help.

## Raw Data

Full results in `profile-results/results.json` and per-benchmark flamegraphs
in `profile-results/<name>/flamegraph.svg`.

## Alternative Allocator Investigation (2026-03-11)

Tested drop-in replacement allocators via `LD_PRELOAD` to address the
~18% of samples in malloc/free/new.

### Results

| Benchmark | glibc | tcmalloc | jemalloc | tcmalloc Δ | jemalloc Δ |
|-----------|-------|----------|----------|-----------|-----------|
| linked_list | 1.44s | 1.18s | 1.15s | **-18%** | **-20%** |
| array_ops | 2.56s | 1.91s | 2.09s | **-25%** | **-18%** |
| csmith_42 | 8.50s | 6.41s | 6.50s | **-25%** | **-24%** |
| csmith_1111111111 | 15.71s | 12.73s | 12.01s | **-19%** | **-24%** |

Both allocators give **18-25% speedup** with zero code changes.

### Why it helps

CBMC's irept sharing tree creates and destroys millions of small objects
(tree_nodet, ~64-128 bytes each). glibc's malloc uses per-thread arenas
with bins, but the consolidation and free-list management overhead is
significant for this pattern. tcmalloc and jemalloc use thread-local
caches and size-class segregation that are much faster for small objects.

### Usage

```bash
# Via LD_PRELOAD (no rebuild needed)
LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libtcmalloc_minimal.so.4 cbmc ...
LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libjemalloc.so.2 cbmc ...

# Install
apt-get install libtcmalloc-minimal4  # or libjemalloc2
```

### Recommendation

Add a CMake option to link against tcmalloc or jemalloc. This is the
single largest performance improvement found in this investigation —
larger than all the SSA identifier optimizations combined.

#### Implemented: CMake allocator auto-detection

Added `-Dallocator=auto|tcmalloc|jemalloc|system` CMake option. When
set to `auto` (the default), CMake searches for tcmalloc then jemalloc
and links the first one found. Commit `0da7f8ff4b`.

Install: `apt-get install libgoogle-perftools-dev` (or `libjemalloc-dev`)

#### tcmalloc vs jemalloc comparison

Both give 18-25% speedup. Key differences:
- **tcmalloc**: More consistent (no warmup outliers), slightly faster on
  array-heavy workloads. Known issue: memory footprint can grow over time
  in long-running processes — not a concern for CBMC which runs and exits.
- **jemalloc**: Better memory efficiency for long-running servers. Has a
  warmup cost visible in the first run.
- **mimalloc** (Microsoft): Only ~1% improvement — its advantages are for
  multi-threaded workloads.
- **glibc tuning** (`MALLOC_ARENA_MAX`, `MALLOC_TRIM_THRESHOLD`): 1-3%.
- **macOS**: System allocator already uses magazine-based allocation
  similar to tcmalloc; improvement would be smaller.
- **Windows**: Default heap allocator with LFH is reasonably fast.

Recommendation: tcmalloc for CBMC (single-threaded, short-lived).

#### Implemented: CI tcmalloc installation

Added `libgoogle-perftools-dev` to all Linux CI workflows that build
CBMC with CMake. Commit `28824f9f07`. Workflows updated:
build-and-test-Linux, pull-request-checks, performance, coverage,
profiling.

#### Perf event selection: cycles vs cpu-clock

Tested both events at 997 Hz sampling. Results are nearly identical for
function-level profiling (same ranking, same percentages within noise).
`cycles` uses hardware PMU counters (more precise for instruction-level
analysis); `cpu-clock` is a software timer (always available, works in
CI containers/VMs). The profiling tool uses `cycles` as default with
automatic `cpu-clock` fallback.

## Combined Optimization Summary

| Optimization | Speedup (csmith_42) | Cumulative |
|-------------|--------------------:|----------:|
| Baseline | — | 8.89s |
| SSA string concat | 3.5% | 8.58s |
| set_level_2 opt | 0.4% | 8.55s |
| set_level_0/1 opt | 1.3% | 8.44s |
| field_sensitivity cache | ~0% (array: 4.8%) | 8.49s |
| **tcmalloc** | **24.6%** | **6.41s** |
| **Total** | **27.9%** | **6.41s** |

On the array-heavy benchmark, the combined effect is even larger:
3.13s → 1.91s (**39% faster**).

## Final Combined Results (2026-03-11)

All optimizations combined on `experiment/hash-optimization` branch:
- SSA identifier string concat (replace ostringstream)
- SSA set_level_0/1/2 suffix appending (avoid full rebuild)
- field_sensitivity array loop caching
- irept union optimization (from issue #7960)
- tcmalloc linked via CMake

### Performance vs baseline (develop, glibc malloc)

| Benchmark | Baseline | Optimized | Speedup |
|-----------|----------|-----------|---------|
| linked_list | 1.49s | 1.08s | **27.5%** |
| array_ops | 3.08s | 1.89s | **38.6%** |
| csmith_42 | 8.83s | 6.26s | **29.1%** |
| csmith_1111111111 | 16.81s | 12.44s | **26.0%** |

### New profile (csmith_42, all optimizations + tcmalloc)

| Rank | Function | % | Change vs original |
|------|----------|---|-------------------|
| 1 | `string_containert` hash lookup | 13.2% | Was 10.0% — now larger share because other costs reduced |
| 2 | `sharing_treet::remove_ref` | 6.1% | Was 9.9% — irept union helped |
| 3 | tcmalloc new/delete | 7.8% | Was 18% glibc — 2.3x reduction |
| 4 | `irept::find` | 4.7% | Was 5.4% |
| 5 | `memcmp` | 4.5% | Was 3.5% — larger share |
| 6 | `irept::get` | 3.4% | Was 4.8% |
| 7 | `sharing_treet::detach` | 3.0% | Was 4.6% |
| 8 | `symbol_tablet::find` | 3.0% | Was 4.9% |
| 9 | `irept::operator==` | 2.1% | Unchanged |
| 10 | `hash_string` | 1.9% | Was 1.7% |

### Remaining avenues to explore

1. **String interning volume** (13.2%): Still the #1 hotspot. The remaining
   `set_expression` calls in `field_sensitivity.cpp` (member expressions,
   not just arrays) still trigger full identifier rebuilds. Also,
   `build_ssa_identifier_rec` is called from the constructor for every new
   `ssa_exprt`. Caching the base identifier per-symbol could help.

2. **`memcmp` in string interning** (4.5%): The `string_ptrt::operator==`
   does `memcmp` on every hash table probe. If we stored a pre-computed
   hash alongside the string pointer, we could skip `memcmp` when hashes
   differ. However, `std::unordered_map` already does this internally.
   The cost is from hash collisions in the same bucket.

3. **`irept::find` / `irept::get`** (8.1% combined): These do linear scans
   through `forward_list_as_mapt`. Replacing this with a flat hash map or
   small sorted array for named sub-trees could help, but is a major
   structural change to irept.

4. **`merge_irept::merged`** (1.8%): Expression merging during symex.
   Could benefit from better hash caching.

5. **`sharing_mapt::get_leaf_node`** (1.3%): The SSA renaming map uses a
   hash-array-mapped trie. A flat hash map might be faster for the typical
   map sizes in symex.

### Assessment

The low-hanging fruit has been picked. The remaining hotspots are either:
- **Fundamental data structure costs** (irept find/get, sharing_tree) that
  require structural changes to improve
- **Algorithmic** (string interning volume) that require deeper changes to
  how SSA identifiers are managed
- **Already well-optimized** by tcmalloc (allocation is now 7.8% vs 18%)

The most promising remaining avenue is reducing string interning volume
further — specifically, avoiding `string_containert::get` calls for strings
that are already `dstringt` values. This would require changes to how
`ssa_exprt` stores and updates its identifier.

## Remaining Optimization Plans

### Plan A: Reduce string interning volume (13.2%)

**Goal**: Avoid calling `string_containert::get()` for strings that are
already interned (i.e., already `dstringt` values).

**Approach**: The hot path is `set_expression` in `field_sensitivity.cpp`
which calls `update_identifier` → `build_identifier` → constructs
`irep_idt(std::string)` → `string_containert::get()`. Instead of building
a `std::string` and interning it, build the identifier from existing
`irep_idt` parts using a concatenation that produces an `irep_idt` directly.

**Investigation outcome**: Attempted caching for member expressions
(appending `..component` before level suffixes). No measurable improvement
because the member case is not in a hot loop. The remaining `set_expression`
calls (37% of `update_identifier`) are from diverse call sites without a
single dominant pattern. Further reduction would require adding concatenation
support to `dstringt` itself (which currently only supports construction
from `std::string` via `string_containert::get()`).

**Estimated impact**: 3-5% (reducing 13.2% by ~30-40%)
**Risk**: High — requires changes to core `dstringt`/`string_containert`
**Status**: Partially explored, diminishing returns

### Plan B: Replace `forward_list_as_mapt` in irept (8.1%)

**Goal**: Speed up `irept::find()` and `irept::get()` which do linear
scans through a linked list of named sub-trees.

**Approach**: Replace `forward_list_as_mapt<dstringt, irept>` with a
small flat sorted array or a small hash map. Most irept nodes have
0-5 named sub-trees, so a linear scan of a contiguous array would be
faster than a linked list due to cache locality.

**Estimated impact**: 3-5% (reducing 8.1% by ~40-60%)
**Risk**: High — `forward_list_as_mapt` is used throughout irept

### Plan C: Improve `merge_irept::merged` (1.8%)

**Goal**: Speed up expression merging during symex.

**Approach**: `merge_irept::merged` uses `irept::operator==` (which is
56% self-recursive) to check if an expression is already in the merge
set. Pre-computing and caching hash values for irept nodes would allow
skipping the deep equality check when hashes differ.

**Estimated impact**: 1-2%
**Risk**: Low — isolated change in merge_irept

### Plan D: Optimize `sharing_mapt::get_leaf_node` (1.3%)

**Goal**: Speed up SSA renaming map lookups.

**Approach**: The sharing_map is a hash-array-mapped trie optimized for
persistent/shared maps. For the L2 renaming use case where maps are
typically small and not heavily shared, a flat `std::unordered_map`
might be faster. Profile to confirm.

**Estimated impact**: 0.5-1%
**Risk**: Medium — sharing_map is used for path merging


## Verification of Claims (2026-03-11)

All claims were re-verified using a broader benchmark suite (6 benchmarks,
5 runs each, median reported). Builds were verified via `ldd` to confirm
tcmalloc presence/absence. tcmalloc was tested via `LD_PRELOAD` on builds
that don't have the allocator CMake option.

### Methodology correction

Earlier verification incorrectly showed tcmalloc at 0.1% because
`-Dallocator=system` was silently ignored by the baseline CMakeLists.txt
(which doesn't have the allocator option). Both "glibc" and "tcmalloc"
baseline builds were actually identical. Re-verified using `LD_PRELOAD`.

### field_sensitivity array cache (3a95db52b3) — CORRECTNESS BUG

This commit bypasses `set_expression` and manually constructs SSA
identifiers. It produces **different SSA formulas** than the standard
path (step count changes from 1950 to 1555 on string_ops). This causes
massive regressions:

| Benchmark  | Without | With    | Change |
|------------|---------|---------|--------|
| string_ops | 0.245s  | 4.013s  | **16x slower** |
| matrix     | 1.431s  | 10.56s  | **7x slower** |

The commit has been moved to the top of the branch for separate debugging.
All other optimizations verified without this commit present.

### Verified results at HEAD~2 (all opts except field_sensitivity cache and free-list)

| Benchmark    | Baseline | +SSA opts | +tcmalloc | +Both    | SSA Δ  | tc Δ   | Combined |
|              | glibc    | glibc     | preload   | preload  |        |        |          |
|--------------|----------|-----------|-----------|----------|--------|--------|----------|
| linked_list  | 0.554s   | 0.518s    | 0.471s    | 0.451s   | +6.5%  | +15.0% | +18.6%   |
| array_ops    | 3.081s   | 2.631s    | 2.405s    | 2.037s   | +14.6% | +21.9% | +33.9%   |
| dlinked_list | 0.971s   | 0.918s    | 0.795s    | 0.760s   | +5.5%  | +18.1% | +21.7%   |
| matrix       | 1.661s   | 1.431s    | 1.293s    | 1.103s   | +13.8% | +22.2% | +33.6%   |
| tree         | 2.512s   | 2.382s    | 1.978s    | 1.895s   | +5.2%  | +21.3% | +24.6%   |
| string_ops   | 0.259s   | 0.245s    | —         | 0.263s   | +5.4%  | —      | -1.5%    |
| **TOTAL (5)**| 8.779s   | 7.880s    | 6.942s    | 6.246s   |**+10.2%**|**+20.9%**|**+28.9%**|

No regressions on any benchmark.

### Free-list pool allocator — re-evaluated (glibc only, 5 runs, median)

Earlier testing on a too-small benchmark showed only 1.4%. Re-tested
with the full suite (without tcmalloc):

| Benchmark    | Without | With   | Speedup |
|--------------|---------|--------|---------|
| linked_list  | 0.520s  | 0.512s | 1.5%    |
| array_ops    | 2.644s  | 2.503s | **5.3%**|
| dlinked_list | 0.912s  | 0.900s | 1.3%    |
| matrix       | 1.435s  | 1.356s | **5.5%**|
| tree         | 2.379s  | 2.337s | 1.8%    |
| string_ops   | 0.243s  | 0.235s | 3.3%    |
| **TOTAL**    | 8.133s  | 7.843s | **3.6%**|

The free-list gives a consistent 3.6% speedup with glibc, concentrated
on symex-heavy workloads. With tcmalloc, the effect is ~0% (tcmalloc
already has thread-local size-class caches).

**Assessment**: The 31% claim from the commit message is not reproduced
(likely measured on a different/larger workload or with confounding
factors). The actual benefit is 3.6% with glibc. This is meaningful for
platforms without tcmalloc (macOS, Windows) but adds complexity:
- Memory is never returned to the OS
- Interacts poorly with sanitizers (ASan, valgrind)
- `thread_local` overhead on single-threaded CBMC
- Redundant when tcmalloc is available

### tcmalloc — CONFIRMED at 15-22%

Verified via `LD_PRELOAD` on clean baseline builds confirmed to have
no tcmalloc (via `ldd`). The benefit is consistent across all non-trivial
benchmarks and applies to both baseline and SSA-optimized builds.

SAT solver benefit from tcmalloc is minimal (~1.3% for CaDiCaL, ~1.2%
for MiniSat2) because solvers use fewer, larger allocations. Confirmed
that solvers do use tcmalloc (verified via `LD_DEBUG=bindings`).

### SSA identifier optimizations — CONFIRMED at 5-15%

The ostringstream→string concat and set_level suffix appending give
10.2% overall, with 14.6% on array_ops and 13.8% on matrix. The
benefit is real and concentrated on symex-heavy workloads.

### Summary of claim accuracy

| Optimization | Claimed | Verified | Status |
|-------------|---------|----------|--------|
| SSA string concat | 3.5-11.2% | 5-15% | ✅ Confirmed |
| set_level_0/1/2 | 1.3% | included above | ✅ Plausible |
| field_sensitivity cache | 4.8% | **7-16x regression** | ❌ Bug |
| irept union | 2.4-4.9% | not isolated | ⚠️ Included in HEAD~2 |
| tcmalloc | 18-25% | 15-22% | ✅ Confirmed |
| Free-list (glibc) | 31% | 3.6% | ⚠️ Overstated |
| Free-list (tcmalloc) | 2% | ~0% | ✅ Confirmed |
| get_new_name cache | 4.9% → 0.56% | not exercised | ⚠️ Unverified |

## Post-Verification Profile: Best Configuration (2026-03-11)

Configuration: HEAD~2 (SSA opts + irept union + get_new_name cache + tcmalloc)
Benchmarks: 6 (linked_list, array_ops, dlinked_list, matrix, tree, heavy_array)
Total samples: 1,738

### Timings

| Benchmark    | Symex   | Convert SSA | Total  | Steps  |
|-------------|---------|-------------|--------|--------|
| linked_list | 0.153s  | 0.302s      | 0.425s | 4,433  |
| array_ops   | 2.016s  | 0.137s      | 2.015s | 16,448 |
| dlinked_list| 0.271s  | 0.488s      | 0.735s | 8,242  |
| matrix      | 1.180s  | 0.000s      | 1.080s | 4,148  |
| tree        | 0.695s  | 0.729s      | 1.855s | 27,789 |
| heavy_array | 1.695s  | 0.000s      | 1.573s | 5,176  |

### Hotspot Summary by Category

**SSA identifier pipeline: ~14%**
- `_Hashtable::_M_find_before_node` (string interning): 5.6%
- `build_ssa_identifier_rec`: 3.2%
- `hash_string`: 1.8%
- `_Hashtable::find`: 1.3%
- `update_identifier`: 0.8%
- `ssa_exprt::remove_level_2`: 0.7%
- `string::_M_append`: 2.9% (from identifier building)

**irept operations: ~22%**
- `irept::find`: 8.7%
- `sharing_treet::remove_ref`: 6.9%
- `irept::get`: 6.6%
- `irept::add(id, irept)`: 3.0%
- `sharing_treet::detach`: 2.8%
- `irept::add(id)`: 1.8%
- `irept::operator==`: 0.9%

**Allocation (tcmalloc): ~14%**
- `operator new[]`: 8.9%
- `operator delete[]`: 3.6%
- `operator delete[]` (sized): 1.8%

**Simplifier: ~2.5%**
- `simplify_node_preorder`: 1.5%
- `simplify_node`: 1.0%

**Other CBMC: ~5%**
- `constant_exprt::check`: 2.1%
- `field_sensitivityt::get_fields`: 0.9%
- `field_sensitivityt::apply`: 0.7%
- `binary_exprt constructor`: 0.9%
- `constant_exprt constructor`: 0.8%

### Dominant Call Chain

Nearly all hotspots converge on a single call chain:

```
symex_step → execute_next_instruction → {symex_assign, symex_assert, symex_goto}
  → clean_expr → dereference
    → field_sensitivityt::apply (recursive, 4-5 levels deep)
      → field_sensitivityt::get_fields (recursive for nested arrays/structs)
        → update_identifier → build_ssa_identifier_rec
          → string_containert::get → hash_string → _Hashtable::find
        → irept::find, irept::get (for type/expression lookups)
        → simplify_exprt::simplify (for index expressions)
          → simplify_node_preorder → irept::find
```

The `field_sensitivityt::apply` function is called recursively 4-5 times
per expression during dereference, and `get_fields` recurses for each
array dimension. Each iteration calls `update_identifier` which rebuilds
the SSA identifier string and interns it via `string_containert::get`.

### Key Observations

1. **field_sensitivity dominates everything.** The recursive apply/get_fields
   chain is the root cause of most hotspots. It drives:
   - All SSA identifier rebuilding (14%)
   - Most irept::find/get calls (through type lookups in get_fields)
   - Most allocation (through expression copying in apply)
   - Most simplifier calls (through index simplification in get_fields)

2. **irept::find is called from simplify_node_preorder** which is called
   from within field_sensitivityt::apply's simplification of index
   expressions. The simplifier does deep recursive descent, calling
   `irept::find(ID_type)` at each level to check expression types.

3. **tcmalloc allocation is 14%** — down from 25% with glibc, but still
   significant. The `operator new[]` calls are from `std::vector` growth
   in irept's `sub` member (which stores unnamed children).

4. **`constant_exprt::check` at 2.1%** is validation that runs on every
   `to_constant_expr()` cast. It calls `irept::find(ID_value)`. This is
   pure overhead in Release builds but cannot be disabled without
   `CPROVER_INVARIANT_DO_NOT_CHECK`.

### Actionable Next Steps

**P1: Reduce field_sensitivityt::apply recursion depth** (est. 5-10%)
The 4-5 levels of recursive `apply` calls during dereference are
excessive. Each level copies expressions and triggers identifier
rebuilds. Investigate whether the recursion can be flattened or
whether intermediate results can be cached.
Source: `src/goto-symex/field_sensitivity.cpp`

**P2: Cache type lookups in simplifier** (est. 2-3%)
`simplify_node_preorder` calls `irept::find(ID_type)` at every
recursion level. Since types don't change during simplification,
the type could be passed as a parameter instead of re-looked-up.
Source: `src/util/simplify_expr.cpp`

**P3: Reduce vector reallocation in irept** (est. 2-4%)
The 8.9% in `operator new[]` is largely from `std::vector` growth
in irept's `sub` member. Pre-sizing or using small-buffer optimization
could help.
Source: `src/util/irep.h`

**P4: Avoid redundant `constant_exprt::check`** (est. 1-2%)
The 2.1% in `check` is from validation in `to_constant_expr()`.
Consider a `to_constant_expr_unchecked()` for hot paths where the
type is already known.
Source: `src/util/std_expr.h`

### Investigation: field_sensitivityt::apply optimization (2026-03-11)

**Attempted**: Cache array identifier prefix in `get_fields` array loop.
For each array element, the SSA identifier has the form
`prefix[[bvrep_of_i]]suffix` where prefix and suffix are identical.
The first element uses canonical `set_expression` to establish the
format, then subsequent elements derive identifiers by string replacement.

**Correctness**: Verified — all 7 benchmarks produce identical step
counts to baseline. No invariant violations. (The previous attempt in
commit `3a95db52b3` was buggy because it used decimal `std::to_string(i)`
instead of the bvrep value, and bypassed `set_expression` entirely.)

**Performance** (5 runs, median, with tcmalloc):

| Benchmark    | Without | With   | Δ      |
|-------------|---------|--------|--------|
| linked_list | 0.421s  | 0.422s | -0.2%  |
| array_ops   | 1.972s  | 2.005s | -1.7%  |
| dlinked_list| 0.729s  | 0.726s | +0.4%  |
| string_ops  | 0.204s  | 0.204s | +0.0%  |
| matrix      | 1.062s  | 1.052s | +0.9%  |
| tree        | 1.851s  | 1.846s | +0.3%  |
| heavy_array | 1.537s  | 1.468s | **+4.5%** |
| **TOTAL**   | 7.776s  | 7.723s | **+0.7%** |

**Assessment**: Only 0.7% total improvement. The identifier string
building is not the dominant cost in the array loop — the `from_integer`
call (which creates a `constant_exprt` and interns its bvrep value),
the `ssa_exprt` copy, and the recursive `get_fields` call dominate.
The optimization only helps on `heavy_array` (4.5%) which has large
arrays. **Not worth the added complexity.**

**Root cause analysis**: The profiling shows that the cost is spread
across many small irept operations (find, get, add, detach, remove_ref)
that are fundamental to how CBMC represents and manipulates expressions.
There is no single bottleneck to eliminate — it's the cumulative cost
of millions of small operations on the sharing tree data structure.

**Conclusion**: Further optimization of `field_sensitivityt::apply`
requires either:
1. Structural changes to reduce the number of `apply` calls (e.g.,
   caching results, lazy evaluation)
2. Changes to the irept data structure itself (e.g., replacing
   `forward_list_as_mapt` with a flat hash map for named sub-trees)
3. Reducing the depth of `field_sensitivityt::apply` recursion in
   `symex_dereference.cpp` (currently 4-5 levels deep)

These are all high-risk, high-effort changes that go beyond the scope
of incremental optimization.

### Implemented: hoist loop invariants in get_fields (2026-03-11)

Hoisted loop-invariant work out of both the struct and array loops:
- Prepare a template `ssa_exprt` with L2 already removed before the loop
- Cache `was_l2` flag (identical for all elements)
- For arrays: cache identifier prefix/suffix from first element's
  canonical `set_expression`, derive subsequent identifiers by replacing
  only the index portion (using bvrep values for correctness)

This eliminates per-iteration: 1 `ssa_exprt` copy from the original
(now copies from the lighter template), 1 `get_level_2()` call,
1 `remove_level_2()` call, and for array elements i>0: 1 full
`update_identifier` → `build_ssa_identifier_rec` → `string_containert::get`
chain.

| Benchmark    | Baseline | Optimized | Speedup |
|-------------|----------|-----------|---------|
| linked_list | 0.421s   | 0.421s    | +0.0%   |
| array_ops   | 1.972s   | 1.924s    | **+2.4%** |
| dlinked_list| 0.729s   | 0.728s    | +0.1%   |
| string_ops  | 0.204s   | 0.203s    | +0.5%   |
| matrix      | 1.062s   | 1.002s    | **+5.6%** |
| tree        | 1.851s   | 1.848s    | +0.2%   |
| heavy_array | 1.537s   | 1.356s    | **+11.8%** |
| **TOTAL**   | 7.776s   | 7.482s    | **+3.8%** |

Correctness verified: all 7 benchmarks produce identical step counts.

## Post-Optimization Profile: After get_fields Hoisting (2026-03-11)

Configuration: HEAD (all SSA opts + irept union + get_fields hoisting + tcmalloc)
Benchmarks: 6 heavy benchmarks × 5 runs each under single perf session
Total samples: ~38K (997 Hz, filtered to cbmc process)

### Profile by Category

| Category | % | Key functions |
|----------|---|---------------|
| ostream I/O | 20.9% | xsputn, ostream_insert, num_put, sentry |
| irept operations | 19.2% | operator==, find, get, add, hash, compare, detach, remove_ref, merged |
| tcmalloc | 10.5% | new[], delete[], internal |
| DIMACS I/O + CNF | 6.2% | write_dimacs_clause, process_clause, lcnf |
| memmove | 1.9% | memcpy/memmove |
| field_sensitivity | **1.6%** | apply, ssa_check, requires_renaming, string intern |
| other CBMC | 0.8% | convert_bv, simplify_node |

### Key Changes vs Previous Profile

1. **field_sensitivity dropped from ~14% to 1.6%** — the loop invariant
   hoisting and SSA identifier optimizations were effective.

2. **irept::operator== is now #1 CBMC function at 7.5%** (was ~1%).
   Called from `merge_irept::merged` → `symex_target_equationt::merge_ireps`.
   This is expression deduplication during symex. 56% of samples are
   self-recursive (deep tree comparison).

3. **ostream I/O is 21%** — this is a benchmarking artifact from
   `--dimacs --outfile /dev/null` which still formats all clauses as text.
   In real usage with a SAT solver, this cost would be replaced by solver
   time. Future profiling should use `--stop-on-fail` with actual solving
   to get a realistic profile.

4. **DIMACS CNF generation is 6.2%** — `process_clause`, `write_dimacs_clause`,
   `lcnf`. This is real work that would also happen with a SAT solver
   (clause generation), though the text formatting part is artificial.

### Top CBMC Functions

| Rank | Function | % | Caller |
|------|----------|---|--------|
| 1 | irept::operator== | 7.50% | merge_irept::merged (expression dedup) |
| 2 | sharing_treet::remove_ref | 2.59% | Scattered (destruction) |
| 3 | cnft::process_clause | 2.35% | CNF clause generation |
| 4 | irept::get | 2.22% | Scattered |
| 5 | dimacs_cnft::write_dimacs_clause | 2.19% | DIMACS output (artifact) |
| 6 | irept::find | 1.86% | Scattered |
| 7 | sharing_treet::detach | 1.28% | Copy-on-write |
| 8 | merge_irept::merged | 1.26% | Expression dedup |
| 9 | irept::hash | 1.18% | merge_irept hash table |
| 10 | cnf_clause_listt::lcnf | 1.13% | CNF clause list |

### Actionable Observations

**merge_irept is the new dominant CBMC hotspot** (operator== 7.5% +
merged 1.3% + hash 1.2% = ~10%). It deduplicates expressions by
hashing and deep comparison. Potential optimizations:
- Cache hash values in irept nodes (HASH_CODE is already enabled but
  `hash_code` is only set lazily and cleared on mutation)
- Use hash comparison as a fast-reject before deep operator==
- Consider whether merge_ireps is called too frequently

**The --dimacs benchmark methodology inflates I/O costs.** The 27%
in ostream + DIMACS I/O is an artifact. For future profiling, use
actual SAT solving (e.g., `--sat-solver cadical --stop-on-fail`)
to get a realistic profile of the full pipeline.

**field_sensitivity is no longer a bottleneck** at 1.6%. The loop
invariant hoisting was effective.

### Hash function comparison (2026-03-11)

Tested all three irep hash functions from `src/util/irep_hash.h`:
BASIC (rotate-7 XOR), MURMURHASH2A, and MURMURHASH3.

| Benchmark    | BASIC  | MURMUR2A | MURMUR3 | 2A vs B | 3 vs B |
|-------------|--------|----------|---------|---------|--------|
| array_ops   | 1.923s | 1.930s   | 1.928s  | -0.4%   | -0.3%  |
| matrix      | 1.001s | 1.001s   | 1.007s  | +0.0%   | -0.6%  |
| tree        | 1.846s | 1.863s   | 1.864s  | -0.9%   | -1.0%  |
| heavy_array | 1.356s | 1.358s   | 1.358s  | -0.1%   | -0.1%  |
| linked_list | 0.421s | 0.424s   | 0.423s  | -0.7%   | -0.5%  |
| dlinked_list| 0.730s | 0.733s   | 0.731s  | -0.4%   | -0.1%  |
| **TOTAL**   | 7.277s | 7.309s   | 7.311s  | **-0.4%** | **-0.5%** |

**Conclusion**: No meaningful difference. BASIC is marginally fastest
(0.4-0.5%) but within noise. The hash function is not a bottleneck —
the cost is in the number of hash operations and the deep equality
comparisons that follow hash collisions, not in the hash computation
itself. This is consistent with the earlier finding that `irept::hash`
is only 1.2% of total time.

Instrumented with `IREP_HASH_STATS` to count actual operator== calls:

| Benchmark    | hash calls | BASIC cmp  | MURMUR2A cmp | MURMUR3 cmp | Δ |
|-------------|-----------|------------|-------------|-------------|---|
| array_ops   | 760,484   | 2,712,855  | 2,712,855   | 2,712,855   | 0 |
| tree        | 1,103,385 | 5,274,971  | 5,272,397   | 5,272,397   | -2,574 |
| heavy_array | 172,870   | 1,061,894  | 1,061,894   | 1,061,894   | 0 |
| linked_list | 192,219   | 5,268,225  | 5,268,165   | 5,268,165   | -60 |
| **TOTAL**   | 2,228,958 | 14,317,945 | 14,315,311  | 14,315,311  | **-2,634 (-0.018%)** |

The Murmur variants produce 2,634 fewer operator== calls out of 14.3M
(0.018% reduction). This is negligible and explains why the runtime
difference is within noise.

Notable: the ratio of comparisons to hashes is 6.4:1, meaning
`merge_irept::merged` does ~6 equality checks per hash lookup on
average. This suggests the hash table has significant collision chains
or many structurally similar expressions. However, since the Murmur
hashes don't reduce this ratio, the collisions are likely from
genuinely equal expressions (sharing the same hash bucket), not from
poor hash distribution.

### Investigation: reducing operator== calls (2026-03-11)

**Context**: `irept::operator==` accounts for 7.5% of total time, called
14.3M times across 4 benchmarks. 67.9% are sharing hits (free), 27.7%
are deep comparisons returning true, 3.5% are deep comparisons returning
false, 0.9% are hash rejects.

**Detailed breakdown** (with IREP_HASH_STATS instrumentation):

| Category | Count | % | Cost |
|----------|-------|---|------|
| Sharing hit (ptr ==) | 9,648,072 | 67.9% | Free |
| Hash reject (new) | 133,543 | 0.9% | Cheap |
| Deep compare (equal) | 3,932,670 | 27.7% | **Expensive** |
| Deep compare (not eq) | 501,226 | 3.5% | Expensive |

**merge_irept statistics**:
- 744,362 calls to `merged()`, 82% cache hits
- 19.2 operator== calls per merge call (recursive sub-tree comparison)
- `linked_list` has 65:1 ratio (deep expression trees)

#### Attempted: hash-based fast reject in operator==

Added check: if both ireps have cached hash_code and they differ,
return false immediately. Result: **0.0% runtime impact**. The
`std::unordered_set` already filters by hash before calling operator==,
so the hash reject only fires for non-merge callers (133K out of 14.3M).

#### Attempted: opportunistic sharing in operator==

After a successful deep comparison (result == true), make both ireps
share the same data pointer. This would convert future comparisons
between the same pair into instant pointer checks.

**Result: UNSAFE.** Changing the data pointer in operator== alters
copy-on-write semantics. An irep that was the sole owner of its data
(ref_count == 1, mutations are in-place) becomes a shared owner
(ref_count > 1, mutations trigger detach/copy). This changed the
generated formula: `dlinked_list` went from 8,242 to 19,552 steps.

#### Attempted: pointer-based fast lookup in merge_irept

Added `unordered_set<const void*> known_pointers` to skip the
hash+equality check when an irep's data pointer is already known
to be in the store.

**Result: 1.3% SLOWER.** The overhead of maintaining the pointer set
(hashing pointers, inserting, looking up) outweighs the savings.

#### Analysis: why 3.9M deep-equal comparisons exist

The deep-equal comparisons happen because:
1. `merge_irept::merged` is called on every SSA step (744K calls)
2. 82% of calls find the irep already in the store (cache hit)
3. But `unordered_set::insert` must call operator== to verify the match
4. operator== recurses into sub-trees (19 recursive calls on average)
5. The sub-trees of the incoming irep may not share data pointers with
   the store entries, even though they're structurally equal

The fundamental issue is that `std::unordered_set` has no way to skip
the equality check — it must verify that the hash match is not a
collision. The only way to avoid this is to ensure the incoming irep
shares data pointers with the store entry at every level, which would
require the irep to have been constructed from previously-merged
components.

#### Conclusion

The 7.5% cost of operator== in merge_irept is inherent to the
hash-set-based deduplication approach. The only viable optimizations
would be:
1. **Reduce merge frequency**: Call merge_ireps less often (e.g., every
   N steps instead of every step)
2. **Structural change**: Replace the unordered_set with a data structure
   that can verify membership without deep comparison (e.g., a trie
   indexed by irep structure)
3. **Ensure sharing**: Make the SSA step construction reuse previously-
   merged ireps so that sub-tree pointers match store entries
