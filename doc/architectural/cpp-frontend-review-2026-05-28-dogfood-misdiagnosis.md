## Investigation log: dog-food unordered_map cluster (2026-05-28)

After landing the strip-tag fix (`247aca2e8c`) plus the three downstream
fixes, dog-food sat at roughly `12/14/91/0` (clean / noisy / fail / crash).
The largest failure cluster — 58–59 of 91 files — reported

```
instantiating 'std::unordered_map' with <struct string_ptrt, unsigned …>
```

with the cascade running through `_Hashtable_alloc<…>`,
`__aligned_buffer<nil>` and finally an
`invalid application of 'sizeof' to an incomplete type 'struct nil'`
diagnostic.

### Initial (incorrect) hypothesis

`cbmc --cpp17` succeeds on a minimal repro
(`std::unordered_map<dstringt,int> m; m.reserve(10);`).
`goto-cc -std=c++17 -c` on the *same* source file fails with the
`sizeof(nil)` error.  The first hypothesis was that
`gcc_modet::preprocess()` (which double-preprocesses every `.cpp` to a
`.ii` before handing it off to `cpp_languaget::parse`) was missing the
CBMC-specific protective flags applied by `c_preprocess_gcc_clang()` for
direct `.cpp` input — specifically:

```
-D__CPROVER__
-U__cpp_deduction_guides
-U__cpp_char8_t
-D_PSTL_GLUE_MEMORY_DEFS_H=1
-D_PSTL_GLUE_ALGORITHM_DEFS_H=1
-D_PSTL_GLUE_NUMERIC_DEFS_H=1
```

Adding those flags in `gcc_modet::preprocess()` did make the deduction
guides and PSTL headers stop appearing in the `.ii`, but the
`sizeof(nil)` error persisted.  Even more telling: `cbmc --cpp17` on the
*goto-cc-produced* `.ii` (which lacks the protective flags) still
succeeded.

### Actual finding

Instrumenting the typecheck loop in `cpp_typecheck.cpp` revealed:

- Both `cbmc` and `goto-cc` reach `typecheck()` with the same
  94 parse-tree items, the same source-location files, and the same
  `is_system` classification.
- Both emit the `invalid application of 'sizeof'` error message during
  typecheck.
- Both end `cpp_typecheckt::typecheck()` with `error_count == 0`
  (verified by tracing `get_message_count(M_ERROR)` after every phase
  — convert loop, method bodies, contracts, do_not_typechecked,
  provide_stdlib_bodies, clean_up).
- `language_files.typecheck(...)` returns `false` (success) in both
  cases.

So the `sizeof(nil)` error is NOT what's failing the dog-food files.
It's a noisy diagnostic from a system-header item that the
`sfinae_contextt` already rolls back — the message is printed but the
error count is restored to zero on guard destruction.

The actual dog-food blockers are a different, larger set of cascading
template-instantiation issues:

```
arith_tools.cpp:
  instantiating 'std::unordered_map' with <struct string_ptrt, unsigned …>
  instantiating 'std::unordered_map' with <struct dstringt, std::size_t, …>
  instantiating 'invariant_violated_structured' with
    <struct invariant_failedt, const struct basic_string>
    at file src/util/invariant.h line 244
  found no match for symbol 'swap', candidates are: …
```

The first two messages are recoverable noise (same as for the
non-fatal `uo_make.cpp` repro).  The fatal ones are:

1. `invariant_violated_structured<invariant_failedt, const basic_string>`
   from `src/util/invariant.h:244`.  This is CBMC's own
   panic-with-message template; failing to instantiate it on a
   `basic_string` argument indicates the
   `std::forward<Params>(params)...` pack expansion can't be resolved.
2. `found no match for symbol 'swap'` from `<bits/move.h>`.  The
   libstdc++ `std::swap` ADL lookup pulls in candidates that don't
   uniquely resolve in the typecheck context.

These are **different** issues from the strip-tag bug and from the
`sizeof(nil)` noise.  They would need their own investigations.

### Why the misdiagnosis happened

The `sizeof(nil)` error is highly visible because:

- It appears at the top of every failing dog-food file's output, and
- The same surface diagnostic appears regardless of which deeper
  template instantiation actually failed.

But it's a *non-fatal* surface symptom of system-header processing
that CBMC's `sfinae_contextt` already recovers from.  The line of
investigation that conflates "first error message" with "what
caused the file to fail" is misleading here.

### Recommended diagnostic technique going forward

For dog-food triage on a failing `.cpp`, use the BOTTOM of the
goto-cc output (the last non-suppressed error before the
`CONVERSION ERROR`) rather than the top, since system-header
items emit visible-but-recovered errors that shouldn't drive the
investigation.

### Remaining concrete next steps

These are the actual dog-food layers, in approximate impact order:

- **Fixing CBMC's own `invariant_violated_structured` parameter-pack
  instantiation** (~50+ files affected — every file that uses an
  `INVARIANT(…, "string with formatting")` macro under C++17).
- **`std::swap` ADL resolution** when the candidate set comes from
  `<bits/move.h>` (~22 files via `sharing_treet`).
- **`std::optional<exprt>` instantiation** in
  `src/util/substitute_symbols.cpp` (1 file but distinct cascade).
- **Variable templates** like `std::is_trivially_destructible_v`
  (~3–7 files; explicit-cast errors).

### Files reverted / unchanged

No source files were modified during this investigation; the working
tree is clean against
`b177ca0a13 doc: record concepts support limitations in STANDARD_COVERAGE`.
The five fixes from the previous session (`247aca2e8c…b177ca0a13`)
remain landed.
