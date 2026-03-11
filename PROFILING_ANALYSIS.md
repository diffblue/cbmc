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

Further optimization potential remains: caching SSA identifiers when
levels haven't changed, and reducing the number of `update_identifier`
calls (currently called 3 times per L0→L1→L2 rename chain).

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

## Raw Data

Full results in `profile-results/results.json` and per-benchmark flamegraphs
in `profile-results/<name>/flamegraph.svg`.
