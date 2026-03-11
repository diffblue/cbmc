# String Hashing Investigation

Date: 2026-03-11
Branch: `experiment/hash-optimization`
Parent: `profiling-tool` (commit `c87f7b5`)

## Context

The profiling analysis (PROFILING_ANALYSIS.md) identified string interning
as the #1 hotspot at 11.7% of total samples:
- `_Hashtable::_M_find_before_node` (10.0%) — bucket chain traversal
- `hash_string` (1.7%) — the hash function itself
- `_Hashtable::find` (1.6%) — top-level find

## Investigation

### Hash function quality

Tested `hash_string` (h*31+c) vs FNV-1a on 1,429 real CBMC identifiers
from a CSmith benchmark:

| Hash function | Buckets=1429 | Empty | Max chain | Collisions |
|---------------|-------------|-------|-----------|------------|
| hash_string (h*31+c) | 1429 | 525 | 5 | 525 |
| FNV-1a | 1429 | 516 | 5 | 516 |
| sequential (dstringt::no) | 1429 | 0 | 1 | 0 |

**Finding**: Both hash functions have similar distribution quality.
The sequential index used by `dstringt::hash()` is actually perfect
(zero collisions) since consecutive integers distribute uniformly
across power-of-2 bucket counts.

### String container usage patterns

Instrumented `string_containert::get` to measure call frequency:

| Benchmark | get() calls | Hit rate | Unique strings |
|-----------|-------------|----------|----------------|
| linked_list (unwind 200) | 232,972 | 93.0% | 16,257 |
| csmith_42 (unwind 257) | 11,529,458 | 98.6% | 156,682 |

**Finding**: The vast majority of `get()` calls are for already-interned
strings. The cost is not in the hash function but in the sheer volume
of lookups.

### Hash table configuration

At exit, the string container hash table has:
- csmith_42: 156,682 entries, 172,933 buckets, load factor 0.91
- linked_list: 16,257 entries, 20,753 buckets, load factor 0.78

### Experiments

#### Experiment 1: FNV-1a hash function
Replaced `hash_string` (h*31+c, i.e., h = (h<<5)-h+c) with FNV-1a
(h = (h^c) * prime).

**Result**: 9.21s vs 8.89s baseline — **3.6% SLOWER**. The FNV-1a
multiply instruction is more expensive than the shift-subtract, and
the better avalanche properties don't help because chain lengths are
already short.

#### Experiment 2: Pre-reserve hash table (10,000 buckets)
Added `hash_table.reserve(10000)` in the constructor.

**Result**: 8.87s vs 8.89s baseline — **no measurable difference**.
`std::unordered_map` already handles growth with amortized O(1) inserts.

#### Experiment 3: Reduce max load factor to 0.5
Set `hash_table.max_load_factor(0.5)` to double bucket count and
halve average chain length.

**Result**:
- csmith_42: 8.77s vs 8.89s — **1.3% faster**
- csmith_1111111111: 16.60s vs 16.91s — **1.8% faster**

Consistent but modest improvement. Doubles the hash table memory
(~2.6MB → ~5.2MB for 156K entries).

## Root Cause Analysis

The 10% hotspot is NOT caused by:
- Poor hash function quality (distribution is fine)
- High load factor (0.91 is reasonable)
- Hash table sizing (reserve doesn't help)

The root cause is the **volume of redundant string interning calls**.
Every `update_identifier(ssa_exprt&)` call in the symex loop:

1. Creates two `std::ostringstream` objects (heap allocation)
2. Builds the SSA identifier string character by character
3. Calls `oss.str()` → allocates a `std::string`
4. Constructs `irep_idt(std::string)` → calls `string_containert::get()`
5. `get()` hashes the entire string and walks the hash table

This happens 11.5M times on csmith_42, with 98.6% of calls finding
an already-interned string. The `ostringstream` + hash + lookup cost
is paid every time, even though the result is almost always the same.

The call chain is:
```
field_sensitivityt::get_fields / rename / set_indices
  → update_identifier(ssa_exprt&)
    → build_identifier(expr, l0, l1, l2)
      → build_ssa_identifier_rec(expr, l0, l1, l2, oss, l1_object_oss)
      → irep_idt(oss.str())  // string interning here
        → string_containert::get(std::string)
          → hash_string()
          → hash_table.find()
```

## Recommended Optimization

Instead of optimizing the hash table, **avoid redundant `get()` calls**:

### Option A: Cache SSA identifiers in ssa_exprt
When `l0`, `l1`, `l2`, and the original expression haven't changed,
the identifier string is the same. Cache the last computed identifier
and skip `build_identifier` + interning when inputs match.

### Option B: Build identifiers without ostringstream
Replace `ostringstream` with direct string concatenation using
`id2string()` on the component parts. This avoids heap allocation
for the stream buffer and produces the string directly.

### Option C: Reduce update_identifier calls
Audit callers of `update_identifier` to identify cases where the
identifier is being rebuilt unnecessarily (e.g., after operations
that don't change the SSA levels).

**Estimated impact**: Options A or B could reduce the 11.7% string
interning cost by 50-80%, yielding a 6-9% overall speedup.

## Files Examined

- `src/util/string_hash.cpp` — `hash_string()` implementation
- `src/util/string_container.h/.cpp` — `string_containert` hash table
- `src/util/dstring.h` — `dstringt` with `hash() = no`
- `src/util/irep_hash.h` — alternative hash combine functions
- `src/util/ssa_expr.cpp` — `build_identifier`, `update_identifier`
