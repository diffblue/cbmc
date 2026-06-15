\file

Detailed plan: member instantiation for explicitly/extern-instantiated class templates

# Detailed plan: member instantiation for explicitly-instantiated class templates (`extern template`)

**Owner:** — (to be assigned)
**Status:** Inline-member fix shipped (§9). Architecture pivoting to Option B
(lazy on-odr-use) — see §10 (standard verdict) and §11 (scope). Sections 4–5
(Option A) are retained for history but **superseded by §10–§11**.
**Parent documents:**
`doc/architectural/cpp-frontend-plan-lazy-elaboration.md` (lazy member realization),
`doc/architectural/cpp-frontend-review.md` (frontend gaps).
**Regression anchors:**
`regression/cbmc-cpp/cpp11_string_literal_char_access` (now CORE),
`regression/cbmc-cpp/cpp11_string_fill_ctor` (now CORE — see §12).

**Standard anchors (N5008):**

- **[temp.inst]/3.1** — implicit instantiation of a class template
  specialization causes instantiation of the *declarations*, but **not**
  the *definitions*, of its member functions.
- **[temp.inst]/4** — a member's specialization is implicitly instantiated
  when *referenced in a context that requires the member definition to
  exist* (odr-use).
- **[temp.inst] Note 4** — an **inline** function that is the subject of an
  explicit instantiation *declaration* is **not** a declared
  specialization; it must **still be implicitly instantiated when
  odr-used**, only no out-of-line copy is emitted.
- **[temp.explicit]/2** — an explicit instantiation *declaration* begins
  with `extern`.
- **[temp.explicit]/9–10** — an explicit instantiation that names a class
  specialization is also an explicit instantiation of its direct
  non-template members; an explicit instantiation *definition* instantiates
  only members defined at the point of instantiation.
- **[temp.explicit]/12 + Note 4** — an entity that is the subject of an
  explicit instantiation declaration and is odr-used in the TU must have an
  explicit instantiation *definition* **somewhere in the program**;
  otherwise the program is ill-formed, no diagnostic required. This applies
  to inline functions too.

---

## 1. Symptom and motivation

`std::string` stores its length but not its characters. Minimal repros
(see the two KNOWNBUG tests):

| program | `size()` | characters | verdict |
|---|---|---|---|
| `std::string s = "ab";` then `s[0]` | correct | **non-deterministic** | char asserts FAIL |
| `std::string s(3,'x');` then `s[0]` | **wrong** | **non-deterministic** | size + char asserts FAIL |
| `std::string s; s.push_back('x');` then `s[0]` | correct | correct | SUCCESS |
| `s.front()`, `*s.begin()`, `s.c_str()[0]`, `s.data()[0]` on a literal string | — | non-deterministic | all FAIL |

This is a **soundness gap**: the per-character assertions are true at run
time, but CBMC reports them as FAILURE because the constructor never copies
the bytes. `std::string` is the gating correctness bug for common STL
verification, and the same mechanism affects any explicitly-instantiated
library class template.

---

## 2. Root cause (empirically confirmed)

libstdc++ ships `std::__cxx11::basic_string<char>` as an **explicit
instantiation declaration**:

```cpp
extern template class basic_string<char>;   // <bits/basic_string.h>
```

The literal/range constructor path is
`basic_string(const char*)` → `_M_construct(const char*, const char*,
forward_iterator_tag)` → `_S_copy_chars(char*, const char*, const char*)`
→ `_S_copy(char*, const char*, size_t)` → `char_traits<char>::copy`. The
fill path is `_M_construct(size_type, char)`. The copy helpers `_S_copy*`
and the fill `_M_construct` are the members whose bodies go missing.

Instrumentation (since reverted; tree clean) established the precise chain:

1. **`instantiate_template` is never called for the `basic_string<char>`
   *class* itself** — only for its member *templates* (`_M_construct<FwdIt>`,
   `_If_sv`, …). The class is realized through the
   `class_template_symbol` (incomplete instance) +
   `elaborate_class_template` + parser incomplete→complete-swap path.

2. The **deferred-method-conversion loop lives *inside*
   `instantiate_template`** (`cpp_instantiate_template.cpp:3313`–`3360`,
   "Move deferred methods of this class to method_bodies"). Because that
   function is never entered for the class, **the loop never runs for
   `basic_string<char>`'s members.**

3. During class-body type-checking, `typecheck_compound_declarator`
   (`cpp_typecheck_compound_type.cpp` ~2503) routes each inline member to
   `deferred_typechecking` when the enclosing scope is a template scope and
   the class is not flagged `template_class_instance`. For
   `basic_string<char>` the observed flags are `tmplscope=1, instance=0,
   hasargs=0`, so **every inline member lands in `deferred_typechecking`,
   carrying its (un-converted) body.** Trace excerpt:

   ```
   clearing deferred …basic_string<char,…>::_S_copy(ptr_char,ptr_const_char,unsigned_long_int) hadbody=1
   clearing deferred …basic_string<char,…>::_M_construct(this,unsigned_long_int,char)        hadbody=0
   ```

   So `_S_copy` **exists with a body**; the fill `_M_construct(size_t,char)`
   exists as a declaration with **no** body.

4. Nothing converts these deferred members: the on-odr-use trigger in
   `typecheck_expr_function_identifier`
   (`cpp_typecheck_expr.cpp:5321`, guarded by `value.is_not_nil() &&
   deferred_typechecking.count(name)`) does **not** fire for the
   static-member calls between these helpers.

5. Finally `cpp_typecheckt::clean_up()` (`cpp_typecheck.cpp` ~600) reaches
   its `deferred_typechecking` branch and **`make_nil`s the bodies** — "member
   functions in template scopes that were never instantiated". The copy
   becomes a no-op.

**Contrast — why user code works.** A user-written `extern template struct
Box<int>;` followed by any odr-use (`Box<int> b;`) is realized through
`instantiate_template`, whose deferred loop converts the inline members.
Minimal user-level repros covering inline-→inline, **static** inline
helpers, and **out-of-line** callers all verify correctly
(`/tmp/df/extt{1,2,3}.cpp`). The bug is specific to the **elaborate-only
realization path** that `basic_string<char>` takes because it is
forward-declared / explicitly instantiated in system headers and never
flows through `instantiate_template` as a class.

**Net:** the realization path used for explicitly/extern-instantiated class
templates omits the member-definition instantiation step that
`instantiate_template` performs, and `clean_up()` then discards the
un-converted bodies.

---

## 3. Why this is a CBMC-specific obligation (standard grounding)

Under [temp.explicit]/12, an extern-template entity that is odr-used must
have an explicit instantiation *definition* **somewhere in the program**.
For a normal compile+link, that definition lives in the precompiled
`libstdc++.so`. **CBMC analyses a single translation unit and links no such
library**, so it must *itself* supply the definitions by implicit
instantiation. For **inline** members (which all the `basic_string` SSO
helpers are), [temp.inst] Note 4 makes this mandatory regardless of linkage:
they are not declared specializations and **must be implicitly instantiated
when odr-used**.

Therefore the correct behaviour for CBMC is: **an `extern template`
(explicit instantiation *declaration*) must not suppress on-odr-use implicit
instantiation of member *definitions*.** This is exactly the lazy model
already embodied by `deferred_typechecking`; the defect is that the
trigger/loop that converts the deferred bodies is bypassed for the
elaborate-only realization path, and the cleanup step then deletes them.

CBMC already eagerly converts *all* deferred inline members of a normal
instance (in `instantiate_template`'s deferred loop) rather than strictly
on first odr-use. That is a sound superset of [temp.inst]/3.1 (it realizes
definitions the standard would defer to odr-use) and is the existing,
tested behaviour. The fix should make the elaborate-only path **consistent
with that existing behaviour**, not invent a new policy.

---

## 4. Design options

### Option A — run the deferred-conversion loop on the elaborate-only path (recommended)

Make `elaborate_class_template` (and/or the incomplete→complete swap in
`typecheck_compound_type`) perform the **same** member-body conversion that
`instantiate_template` already performs at
`cpp_instantiate_template.cpp:3313`–`3360`: after the class instance is
complete, move its `deferred_typechecking` members into `method_bodies` and
convert them, recursively, with the instance's template map established.

- **Pros:** reuses the existing, tested conversion loop; keeps a single
  policy ("an instance's inline member bodies are converted once the
  instance is realized"); naturally recursive (converting `_S_copy_chars`
  enqueues `_S_copy`, which enqueues `char_traits<char>::copy`, …) via the
  existing `method_bodies` worklist.
- **Cons:** requires the instance's **template map** (params→args) to be
  available at the elaborate site. `class_template_symbol`
  (`cpp_instantiate_template.cpp:351`–`372`) sets `ID_C_template` and
  `ID_C_template_arguments` on the incomplete symbol, and
  `typecheck_compound_type` (~208) is supposed to preserve them across the
  incomplete→complete swap — **but the realized `basic_string<char>` symbol
  was observed to carry neither**. Step 1 of the work is to determine
  whether the metadata is never set or is lost, and ensure it survives so
  the map can be rebuilt (the same way `instantiate_template` builds it from
  `new_decl.template_type()` + `specialization_template_args`).

### Option B — make the on-odr-use trigger fire for these members (principled, lazy)

Keep bodies deferred and convert each member exactly when first odr-used,
per [temp.inst]/4. Requires diagnosing why
`typecheck_expr_function_identifier` does not fire for the static-member
calls (`_S_copy_chars` → `_S_copy`): the call expression is most likely not
a bare `ID_symbol` at the trigger point (it is resolved through a
member/qualified-name path that bypasses the deferred-body hook), so the
hook must be moved/duplicated onto every call-resolution path (member calls,
static-member calls, qualified calls), and the converted body must be
substituted with the instance's map.

- **Pros:** strictly matches the standard's odr-use timing; converts only
  what is used (smaller symbol tables).
- **Cons:** larger, riskier change touching all call-resolution paths; the
  map-reconstruction problem is identical to Option A; lazy conversion
  mid-`convert_function` re-entrancy is delicate.

### Option C — post-pass before `clean_up` converting deferred members of concrete instances (rejected as primary)

A pass over `deferred_typechecking` (before `clean_up`) that converts
members whose enclosing class is a concrete (non-template) struct.
**Tried experimentally and rejected:** it does give `_S_copy_chars` a body,
but the body's `_S_copy(...)` call resolves to `nil` and is **silently
dropped**, because at conversion time the proper class scope / template map
is not established and `_S_copy` is not yet realized. It also runs too late
to recover the map. Useful only as a safety net, not the fix.

### Option D — `clean_up` converts instead of clears (rejected)

Converting in `clean_up` fails for the same reason as C: the scope and
template map are gone by then, and `_CharT`/`traits_type`/sibling-member
references no longer resolve.

### Recommendation

**Adopt Option A**, with two supporting robustness fixes that are valuable
independent of the main change:

- **R1 — never silently drop a call to an unresolved member.** When
  call-resolution yields `nil` for what should be a member function, this
  must trigger instantiation-on-demand or raise a diagnostic — never emit an
  empty statement. The current silent drop is what masks the bug as
  "verifies but wrong" rather than a clear error. (This is the mechanism
  behind the dropped `_S_copy` call in Option C.)
- **R2 — `clean_up` must not discard the body of a member belonging to a
  fully-realized concrete instance.** Only genuine, never-instantiated
  *class-template* members (enclosing class still a template) should be
  nilled. A member of a complete concrete struct that still has an
  un-converted body indicates a missed conversion (defense in depth that
  also surfaces regressions loudly instead of silently).

---

## 5. Implementation steps (Option A)

> **Superseded by §10–§11.** Option A (eager conversion at the
> completion/instantiation site) was partially shipped for inline members
> (§9), but [temp.inst]/11 establishes that eager instantiation of unused
> non-virtual members is non-conforming, and experiments confirmed it
> destabilises the standard library. The plan of record is now Option B
> (§11). This section is kept for historical context.

1. **Pin the metadata gap.** Add temporary instrumentation to confirm
   whether `basic_string<char>` reaches
   `typecheck_compound_type`'s incomplete→complete swap (~208) with
   `ID_C_template` / `ID_C_template_arguments` set, and whether they survive
   the `.swap(type)`. Determine the exact realization path
   (`class_template_symbol` vs a parser-only completion) and where the
   metadata is dropped. *(Acceptance: a definitive statement of where the
   instance loses its template map.)*

2. **Ensure the instance carries its template map.** Where the metadata is
   lost, preserve or reconstruct `ID_C_template` (the primary
   `template_type` with parameters) and `ID_C_template_arguments` (the
   concrete args, derivable from the instance's mangled name if absent), so
   the params→args map can be rebuilt exactly as `instantiate_template`
   does.

3. **Factor out the deferred-conversion loop.** Extract
   `cpp_instantiate_template.cpp:3313`–`3360` into a reusable helper, e.g.
   `convert_deferred_methods_of(const symbolt &class_symbol)`, that:
   (a) establishes the instance's template map (a `cpp_saved_template_mapt`
   guard), (b) moves matching `deferred_typechecking` members to
   `method_bodies`, attaching out-of-line bodies from `template_methods`
   when the in-class body is nil (the existing logic), and (c) drains
   `method_bodies` via the existing conversion path so the recursion
   (`_S_copy_chars` → `_S_copy` → `char_traits<char>::copy`) terminates at
   fixpoint.

4. **Invoke the helper from the elaborate-only path.** Call it once the
   class instance is complete in `elaborate_class_template` (and/or at the
   end of the incomplete→complete swap in `typecheck_compound_type`),
   guarded so it runs only for realized **template instances** (not for
   ordinary user classes, which have no deferred template members) and is
   idempotent (no double-conversion; reuse `methods_seen`).

5. **Robustness R1/R2** as in §4.

6. **Re-validate the two downstream member-body bugs** that the prior
   investigation saw once these paths are actually converted (they are
   *separate* defects, expected to surface as the input-iterator path begins
   to type-check):
   - **Anonymous-union array-member lvalue:**
     `this->…_M_local_buf[i]` (array member inside the SSO anonymous union)
     reported "not an lvalue", contrary to [expr.sub]/[basic.lval].
   - **Out-of-line member-template parameter name:** `__beg` reported
     "unknown" in the out-of-line `_M_construct(_InIterator, _InIterator,
     input_iterator_tag)`.
   These do not block literal/fill construction (which use the
   forward-iterator + `_S_copy_chars` and the `size_type` paths) but should
   be fixed to complete input-iterator construction. File as follow-on
   tasks; do not scope-creep the core fix.

### Primary code touch-points

| file | location | role |
|---|---|---|
| `cpp_instantiate_template.cpp` | 3313–3360 | deferred-conversion loop to extract/reuse |
| `cpp_instantiate_template.cpp` | 259–410 (`class_template_symbol`) | sets instance metadata; ensure map survives |
| `cpp_instantiate_template.cpp` | 880+ (`elaborate_class_template`) | call site for the reused loop |
| `cpp_typecheck_compound_type.cpp` | ~208 (incomplete→complete swap) | metadata preservation; alt call site |
| `cpp_typecheck_compound_type.cpp` | ~2503 (`typecheck_compound_declarator`) | routes inline members to `deferred_typechecking` |
| `cpp_typecheck.cpp` | ~600 (`clean_up`) | R2: do not nil concrete-instance member bodies |
| `cpp_typecheck_expr.cpp` | ~5321 (`typecheck_expr_function_identifier`) | R1 / Option-B trigger |

---

## 6. Risks and mitigations

- **Map reconstruction wrong → mis-substituted member bodies.** Mitigate by
  reusing `instantiate_template`'s exact map-building code, not a
  re-implementation; validate against the full `cbmc-cpp` suite.
- **Eagerly converting all inline members blows up symbol-table size /
  type-check time for large library classes** (`basic_string`, `vector`,
  `map`). Mitigate: only convert members that already sit in
  `deferred_typechecking` for *this* instance (a bounded set), reuse
  `methods_seen` for idempotency, and measure type-check time on the
  dog-food corpus. If cost is prohibitive, fall back to Option B (true
  on-odr-use laziness) for the heavy classes.
- **System-header SFINAE interaction.** Class realization for system headers
  runs under the `sfinae_contextt` try/catch in `cpp_typecheckt::typecheck`.
  Ensure the reused loop's failures on un-modellable members remain
  non-fatal (preserve the existing per-member try/catch) so one bad member
  does not abort the rest — but combine with R1 so genuine drops are not
  silent for *user* code.
- **R2 turning silent wrong-answers into hard errors may expose other
  latent gaps.** That is desirable (soundness over convenience) but may
  produce a batch of newly-loud failures; stage R2 behind the core fix and
  triage.

---

## 7. Validation strategy

1. **KNOWNBUG → CORE flip.** `cpp11_string_literal_char_access` and
   `cpp11_string_fill_ctor` must verify SUCCESSFULLY after the fix;
   reclassify both from `KNOWNBUG` to `CORE` in the same change.
2. **Accessor breadth.** Add CORE coverage for `front()`, `back()`,
   `*begin()`, `c_str()[i]`, `data()[i]`, `at(i)`, range-based-for, and
   `operator==`/`find` on a literal-constructed string.
3. **Construction breadth.** literal, fill `(n,c)`, copy, `substr`,
   `operator+`, `std::to_string`.
4. **Full suite, all standards.** `cpp11/14/17/20/23 -C` plus the complete
   `cbmc-cpp` suite (`-X libcxx`), expecting the established libstdc++
   baseline with the two KNOWNBUGs now CORE-passing and **no** regressions.
   Commit each logical change separately;
   `git-clang-format --binary clang-format-15 --diff HEAD^` must be clean.
5. **No-regression on user-level extern templates.** Keep
   `extt{1,2,3}`-style cases (inline→inline, static helpers, out-of-line
   caller) green.
6. **Dog-food probe.** Re-run the `/tmp/df` STL probe; confirm `std::string`
   moves to SUCCESS and characterize the next correctness item.

### Test matrix

| dimension | values |
|---|---|
| construction | literal `"…"`, fill `(n,c)`, copy, move, `substr`, `operator+`, `to_string` |
| access | `[]`, `at`, `front`, `back`, `begin/end` deref, `c_str`, `data`, range-for |
| standard | `--cpp11`, `--cpp14`, `--cpp17`, `--cpp20`, `--cpp23` |
| library | libstdc++ (`test.desc`), libc++ (`test_libcxx.desc`, `--stdlib libc++`) |

---

## 8. Out of scope

- BMC formula-size scaling for `std::unordered_map`, `std::shared_ptr`, and
  `std::map::operator[]` (a separate performance track, not a frontend
  correctness gap).
- The two downstream member-body defects (anonymous-union lvalue;
  out-of-line member-template parameter name) beyond filing them as

---

## 9. Implementation outcome (2026-06)

A first increment is implemented. Findings refined the design:

- **The metadata is present.** `basic_string<char>` is completed through the
  incomplete→complete swap in `typecheck_compound_type`, and at that point
  the symbol *does* carry `ID_C_template` + `ID_C_template_arguments` +
  `template_class_instance` (an earlier "no metadata" reading was a grep
  artifact on the multi-line type dump). `add_method_body` already rebuilds
  the class template map from those, so routing a deferred member through it
  "just works" for inline members.

- **`elaborate_class_template` is a dead end for this class.** It is called
  hundreds of times for `basic_string<char>` but always returns early (the
  class is already complete), so it never reaches its `instantiate_template`
  call and the deferred-method loop never runs. The fix hooks the
  **instance-completion site** in `typecheck_compound_type` instead.

- **Eager conversion of *all* deferred members is unsafe.** Correcting the
  member-matching inside `instantiate_template`'s own deferred loop (so it
  also matches classes whose template arguments contain `::`, e.g.
  `std::_Hashtable<…,std::__detail::…>`) regressed `std::unordered_map`
  (ambiguous `_Hashtable_ebo_helper`, CONVERSION ERROR) and `std::regex`
  (crash), and a completion-site hook that also fetched **out-of-line**
  bodies by base name regressed `std::valarray` (`operator[]` returned a bad
  pointer, from attaching the wrong overload's body). Converting member
  bodies that are never odr-used surfaces latent frontend bugs.

- **Shipped: the safe inline-only subset.** `instantiate_template` is left
  unchanged. A new `queue_deferred_methods_of_instance(class_id)` is invoked
  at the completion site and queues only the instance's **inline**
  (already-bodied) deferred members via `add_method_body`. The `tag-`
  stripping is corrected to cut the token before the **first `<`**, so
  namespaced template arguments no longer fool it. This fixes literal/range
  construction and every accessor (`[]`, `at`, `front`, `back`, `*begin`,
  `c_str`, `data`) for `std::string` in C++11/14/17 with **no regressions**
  across the full `cbmc-cpp` suite. `cpp11_string_literal_char_access` is now
  CORE.

### Remaining work

1. **Out-of-line members (signature-aware fetch).** *Done for the
   wrong-overload case* — see §12: `instantiate_matching_member_body()` selects
   the out-of-line definition by signature (parameter arity) and the repair is
   gated to genuine wrong-overload attachments, fixing `std::string(n, c)`
   (`cpp11_string_fill_ctor` is now CORE).  Still open: members whose
   *correct* out-of-line body cannot be converted because it transitively
   instantiates something CBMC cannot model (e.g. the `_Hashtable_ebo_helper`
   "does not uniquely resolve" gap) — these remain no-bodied.
2. **C++20/23 `std::string s = "ab"`** currently fails earlier, in
   constructor *resolution* (`CONVERSION ERROR: invalid implicit conversion
   from 'char [3]' to 'struct basic_string'`). This is a pre-existing,
   independent defect (confirmed on the baseline) unrelated to member
   instantiation.
3. **R1/R2 robustness (§4)** were *not* implemented: R2 in particular (making
   `clean_up` convert rather than discard) is a form of eager conversion and
   showed the same destabilisation; both are deferred until the lazy /
   signature-aware paths above make them safe.
  follow-on tasks; they are independent of the instantiation mechanism.

---

## 10. Standard verdict: lazy on-odr-use instantiation is mandatory

Re-reading N5008 settles the architecture: lazy, on-odr-use instantiation of
member function *definitions* is not merely preferable, it is what the
standard prescribes.

- **[temp.inst]/3.1** — implicit instantiation of a class specialization
  instantiates the *declarations*, **not the definitions**, of its member
  functions.
- **[temp.inst]/3.2** — the only member *definitions* instantiated together
  with the class are deleted member functions, unscoped member enumerations,
  and member anonymous unions.
- **[temp.inst]/4, /5** — a member or function definition is implicitly
  instantiated **when odr-used** (referenced in a context requiring the
  definition to exist).
- **[temp.inst]/8 (example)** — `Z<int>::g()` and `Z<char>::f()` are
  explicitly **not** instantiated merely because `Z<int>`/`Z<char>` are.
- **[temp.inst]/11** — the decisive normative rule:

  > "An implementation **shall not** implicitly instantiate a function
  > template, a variable template, a member template, a **non-virtual member
  > function**, a member class or static data member of a templated class …
  > **unless such instantiation is required.**"
  >
  > "It is **unspecified** whether or not an implementation implicitly
  > instantiates a **virtual** member function of a class template if [it]
  > would not otherwise be instantiated."

So eager instantiation of unused **non-virtual** members is *non-conforming*;
**virtual** members are the sole permitted-eager exception (an implementation
may instantiate them, as is natural for the vtable / reachable dispatch).

**Why this matters for CBMC (not pedantry).** A class-template member can be
ill-formed when instantiated for a particular specialization yet the program
is valid as long as the member is not used. Eagerly instantiating it forces
type-checking of a body the program never needs — which is exactly what
produced the earlier regressions (`unordered_map`'s ambiguous
`_Hashtable_ebo_helper` CONVERSION ERROR; the `regex` crash). Those were not
incidental: they are the predictable consequence of doing what [temp.inst]/11
forbids. For a verifier, instantiating exactly the odr-used members is both
standard-aligned and sufficient for soundness, and it removes a whole class of
spurious errors.

**Current state vs. the standard.** CBMC today over-instantiates:
`instantiate_template`'s deferred-method loop converts *all* of an instance's
deferred member bodies, and the shipped completion-site hook (§9) converts an
instance's inline member bodies — both regardless of odr-use. The regression
`cpp17_lazy_inst_unused_not_emitted` demonstrates this directly (an unused
member's assertion enters the goto program). It is tolerated today only
because the conversion error of an ill-formed unused member is usually
*swallowed* (`typecheck_method_bodies` wraps `convert_function` in
`try/catch`) — but swallowing fails for hard errors and cannot catch crashes.

**Conclusion.** Option B (lazy on-odr-use, with eager virtuals) is the correct
target. The completion-site inline-only hook and the eager deferred loop are
stepping stones to be *retired into* Option B, not kept beside it.

---

## 11. Option B: scope and incremental plan

### 11.1 Target behaviour

- A member function definition is instantiated **the first time it is
  odr-used**: a (non-dependent) call, taking its address, an explicit
  instantiation definition, or being a defaulted/needed special member.
- **Virtual** members of an instantiated class are instantiated when the class
  is instantiated (reachable via dispatch; permitted by [temp.inst]/11).
- Members never odr-used are **never** instantiated (no body, no error).
- The instantiation reuses the existing machinery: build the class template
  map from the instance's `ID_C_template` / `ID_C_template_arguments` (as
  `add_method_body` already does), fetch the definition (in-class body, or
  out-of-line from `template_methods` matched **by signature**), substitute,
  and convert.

### 11.2 Reusable core (the signature-aware helper)

A standalone, trigger-agnostic routine:

```
maybe_instantiate_member_definition(symbolt &member, const symbolt &instance)
```

that, given a member with a nil/uninstantiated body belonging to a realized
instance, (a) finds the unique signature-matching definition — in-class or
out-of-line in a primary template's `template_methods`, matched by parameter
signature after instance-map substitution, **not** by base name — (b)
substitutes with the instance map (reusing the existing pack-expansion logic),
and (c) attaches/queues the body. This is the piece that is identical whether
driven eagerly or lazily; build it first.

### 11.3 odr-use trigger sites

- Direct calls: `typecheck_function_call_arguments` /
  `typecheck_method_application` / `typecheck_expr_function_identifier`
  (`cpp_typecheck_expr.cpp`). The existing deferred-typechecking hook at
  `typecheck_expr_function_identifier` (which only fires for non-nil-value
  members) is the natural extension point; it currently does **not** fire for
  some member/static-member call shapes — closing that gap is the crux.
- Address-of a member function.
- Implicitly-called special members (constructors, destructors, assignment).
- Virtual members: instantiate at class instantiation (separate from odr-use).

### 11.4 Incremental steps (each gated by the §11.6 safety net)

1. **Land the safety net** (done): the `cpp17_lazy_inst_*` tests plus the
   existing string tests.
2. **Build the signature-aware helper** (§11.2), unit-exercised against the
   `std::string(n,c)` fill `_M_construct` overload set. **Done** — shipped as
   `instantiate_matching_member_body()` (see §12).
3. **Add the lazy trigger additively**: instantiate on odr-use *in addition to*
   the current eager paths. Nothing should regress.
   *(Correction: `cpp11_string_fill_ctor` is **not** an Option B item.
   Investigation showed its fill `_M_construct` is already instantiated on
   odr-use — the member-call path `typecheck_method_application` already builds
   the class map and calls `add_method_body` — but was attached the **wrong
   overload's** out-of-line body, a downstream conversion bug.  It is fixed
   independently in §12 using the signature-aware helper, and is now CORE.)*
4. **Disable eager instantiation** of non-virtual members (the
   `instantiate_template` deferred loop and the §9 completion hook), relying on
   the lazy trigger. **This is the high-risk step**: tests that passed
   spuriously (because an unused, would-fail member was being instantiated, or
   because an assertion inside an unused body was vacuously satisfied) may flip.
   `cpp17_lazy_inst_unused_not_emitted` should flip to passing here. Triage the
   full suite; expect and investigate movement.
   **Done** — see §13.  The actual mechanism turned out to be simpler and more
   localised than anticipated (a single force-drain in
   `typecheck_method_bodies`, not the `instantiate_template` loop); the
   reachability fallback (§11.5) is what makes it safe.
5. **Eager virtuals**: ensure reachable virtual members are still instantiated
   at class instantiation (`cpp17_lazy_inst_virtual` guards this).  **Done** —
   virtual members are the only members `add_method_body` keeps eager;
   `cpp17_lazy_inst_virtual` stays CORE.  Ordinary methods, operators and the
   special members (constructors, destructors, assignment) are all deferred and
   instantiated only on odr-use — see §13, including how destructor odr-use is
   recovered from the constructed-class set ([class.dtor]/12).
6. **Retire the completion-site hook** (§9) once the lazy path subsumes it;
   re-confirm `cpp11_string_literal_char_access` via the lazy path.
   **Assessed and kept** — disabling the hook makes `std::string` construction
   a no-op again, because the lazy odr-use path does not yet subsume it for
   system-header extern-template instances (their inline members sit in
   `deferred_typechecking`, not `deferred_method_bodies`).  See §13.

### 11.5 Risks

- **Reachability gaps**: missing an odr-use site leaves a needed member
  un-instantiated (no body → unsound). Mitigate by enumerating odr-use sites
  (§11.3) and by a *fallback* late pass that instantiates any member still
  referenced by an emitted call. Bias toward instantiating-when-in-doubt for
  *referenced* members (never for unreferenced ones).
- **Re-entrancy**: lazy instantiation mid-`convert_function` (a call inside a
  body triggers another instantiation) must be safe; the existing
  `method_bodies` worklist already supports this.
- **Spurious-pass churn (step 4)**: the safety net is designed to localise it;
  expect some existing tests to need reclassification (either they reveal a
  real latent bug now correctly surfaced, or they were KNOWNBUG-worthy).

### 11.6 Regression safety net (STL-independent, added with this write-up)

| test | level | property |
|---|---|---|
| `cpp17_lazy_inst_unused_inline` | CORE | unused ill-formed inline member must not error ([temp.inst]/11) |
| `cpp17_lazy_inst_unused_outofline` | CORE | same, out-of-line definition |
| `cpp17_lazy_inst_extern_unused` | CORE | same, under `extern template` (explicit-instantiation path) |
| `cpp17_lazy_inst_virtual` | CORE | virtual member instantiated + dispatched (permitted-eager carve-out) |
| `cpp17_lazy_inst_unused_not_emitted` | KNOWNBUG → CORE | unused member body must not enter the goto program (precise lazy discriminator) |
| `cpp17_lazy_inst_unused_operator` | CORE | unused non-virtual operator must not be instantiated (§13) |
| `cpp17_lazy_inst_unused_ctor` | CORE | unused non-virtual constructor must not be instantiated (§13) |
| `cpp17_lazy_inst_unused_dtor` | CORE | unused non-virtual destructor must not be instantiated; dtor odr-use recovered via [class.dtor]/12 (§13) |

Plus the existing `cpp11_string_literal_char_access` (CORE) and
`cpp11_string_fill_ctor` (now CORE — fixed independently of Option B, see §12).

---

## 12. Downstream fix: signature-matched out-of-line member bodies (2026-06)

`std::string(n, c)` fill construction was a no-op — **not** because of lazy
instantiation, but because of a *wrong-overload body attachment*, which is
independent of the Option B pivot:

- The fill `basic_string<char>::_M_construct(size_type, _CharT)` instance
  member **is** instantiated on odr-use (the member-call path
  `typecheck_method_application` already builds the class template map and
  calls `add_method_body`).
- However it was attached the **input-iterator** `_M_construct` body
  (`basic_string.tcc:173`, which refers to `__beg`), selected by an earlier
  base-name-only match.  Converting that body fails with "symbol '__beg' is
  unknown"; the failure is swallowed by the system-header SFINAE guard and the
  member is left without a body, so the constructor does nothing.

Fix (`instantiate_matching_member_body()` + a repair hook in
`convert_function`): when a class-template instance member's out-of-line body
fails to convert, look in the primary template's `template_methods` for the
definition whose **signature (parameter arity)** matches the member, but only
when the currently-attached body came from a definition of a **different**
arity (a genuine wrong-overload).  Adopt that definition's body and its
parameter names ([dcl.fct]/3) and re-type-check in a fresh scope; any residual
failure falls back to the previous no-body state.  Grounded in N5008
[over.match] and [dcl.fct]/3.

Design points that proved necessary (each caught by the full `cbmc-cpp`
suite during development):

- **Failure-gated, not proactive.** A proactive "always re-fetch the
  signature-matched body" replaced correctly-converting members' bodies and
  regressed `set`, `regex`, `deque`, …  Repairing only on conversion *failure*
  leaves correct members untouched.
- **Different-arity gate.** Arity-only matching still mis-fired on
  `std::_Hashtable` constructor / `operator=` overloads that share an arity;
  converting their (correct-arity) bodies surfaced an unrelated modelling gap
  (`_Hashtable_ebo_helper does not uniquely resolve`).  Restricting the repair
  to members whose *current* body comes from a different-arity definition
  confines it to genuine wrong-overload attachments.
- **Parameter-name adoption.** Even with the right body, the in-class
  declaration and the out-of-line definition may use different parameter names
  (`__req` vs `__n`); the member must adopt the definition's names so the
  body's references resolve.

`instantiate_matching_member_body()` is the reusable, signature-aware core
that the lazy (Option B) work will also drive, but the repair itself is a
contained downstream-conversion fix, not part of the Option B pivot.


---

## 13. Option B implementation outcome (2026-06)

Lazy on-odr-use member instantiation ([temp.inst]/11) is implemented and
validated. The change was smaller and more localised than §11.4 anticipated.

### Where the eager instantiation actually was

`add_method_body()` *already* implements the right policy at queue time: for a
template-instance member that is **not** a constructor, destructor, virtual
member or operator, it parks the body in `deferred_method_bodies` instead of
the immediate `method_bodies` worklist. Constructors, destructors, virtual
members and operators are queued eagerly — virtual is the [temp.inst]/11
permitted-eager carve-out, and the others are pragmatic always-needed cases.

The eager instantiation that violated the standard was a single site at the
end of `typecheck_method_bodies()`: after the on-demand worklist drained, an
**unconditional** loop force-moved *every* remaining `deferred_method_bodies`
entry into `method_bodies` and converted it, justified by a comment that "we
must still process them all because method body type-checking has side
effects". That converted members the program never odr-uses, which is exactly
what [temp.inst]/8 and /11 forbid, and is what admitted an unused member's
assertion into the goto program (`cpp17_lazy_inst_unused_not_emitted`) and
surfaced latent modelling gaps in unused library members (the earlier
`unordered_map` / `regex` breakages).

### The fix (reachability-gated drain)

The unconditional force-drain is replaced by a reachability-gated fixpoint
(`src/cpp/cpp_typecheck_method_bodies.cpp`):

1. Scan every **converted** function body in the symbol table (skipping
   bodies still parked in `deferred_method_bodies`, and `cpp_not_typechecked`
   bodies) and collect the `ID_symbol` identifiers they reference.
2. Emit (move to `method_bodies`) only those still-deferred members that are
   referenced, then drain. The existing function-identifier hook
   (`typecheck_expr_function_identifier`) pulls transitively-referenced
   deferred members in during that drain.
3. Re-scan to a fixpoint. Members that no converted body references are left
   uninstantiated, as the standard requires.

This *is* the §11.5 reachability safety net: a member referenced by emitted
code is instantiated even if its reference shape did not flow through the
odr-use hook, so no needed body is dropped; an unused — possibly ill-formed —
member is never instantiated. Excluding references that originate from
still-deferred (i.e. not-yet-reachable) bodies keeps the reachability set
sound: an unused member that references another member does not keep the
latter alive.

### Why `instantiate_template`'s own loop did not need changing

Members of a class instantiated through `instantiate_template` already reach
`add_method_body` with the instance's `ID_C_template_arguments` set (by the
block right after `convert_non_template_declaration`), so they are deferred
correctly. No change to that loop, nor to the §9 completion hook, was needed;
the fix is confined to the one force-drain.

### Validation

- `cpp17_lazy_inst_unused_not_emitted` flips KNOWNBUG → CORE: the unused
  body's "must never appear" assertion no longer enters the goto program
  (0 occurrences at `--cpp11`/`14`/`17`).
- The rest of the `cpp17_lazy_inst_*` safety net stays CORE, including
  `cpp17_lazy_inst_virtual` (virtuals remain eager and dispatch soundly).
- Full `cbmc-cpp` suite (`-X libcxx`): all pass, no regressions; the string
  literal/fill accessors, the dog-food STL probe, and the user-level
  `extern template` cases (`extt{1,2,3}`) all remain SUCCESSFUL.
- Reachability-scan overhead is negligible (a heavy `unordered_map` test
  type-checks + verifies in ~1.1 s / ~87 MB).

### Residual / follow-on

- **Operators, constructors and destructors are now deferred too** (follow-on,
  done). No non-virtual member is instantiated eagerly any more: ordinary
  methods, operators and the special members all wait for odr-use, leaving
  *virtual* members as the only eager instantiation ([temp.inst]/11). The
  `cpp17_lazy_inst_unused_operator` / `_ctor` / `_dtor` discriminators (all
  CORE) guard this, while heavily-used members such as
  `std::string::operator[]` and a `std::vector`'s constructor/destructor
  remain instantiated because they are odr-used.

  Deferring the special members initially *destabilised container
  verification* (`std::vector` / `std::map` probes timed out in BMC), which a
  goto-program diff root-caused precisely: the lazy `vector` was missing
  exactly its three **destructors** (`~vector`, `~_Vector_base`,
  `~__normal_iterator`) — not a divergent body and not a closure explosion
  (the lazy program had *fewer* functions). Destructor calls for automatic and
  temporary objects are synthesised later, during **goto-conversion**, so the
  destructor's symbol id never appears in the type-checked bodies that the
  reachability scan inspects; the scan therefore could not see the odr-use and
  left `~vector` body-less, which is what made BMC diverge.

  The fix recovers destructor odr-use from the type system rather than from
  body references, grounded in **[class.dtor]/12** (a destructor is
  *potentially invoked* when an object of its class is created): the
  reachability scan collects the set of classes whose **constructors** are
  referenced (`constructed_classes`) and instantiates the destructor of any
  such class. Subobject destructors (`~_Vector_base`, `~__normal_iterator`)
  follow transitively once `~vector`'s body is converted, or via their own
  constructor pairing. This keeps the discriminator sound: a class that is
  only used through a static member (no object constructed, hence no
  constructor odr-used) does not enter `constructed_classes`, so its
  destructor stays uninstantiated.

- **The §9 completion-site inline hook cannot yet be retired** (step 6;
  assessed and **kept**). Disabling `queue_deferred_methods_of_instance`
  makes `std::string` construction a no-op again (the string tests and
  dog-food probes fail). The lazy odr-use path does **not** subsume it for
  system-header *extern-template* instances such as
  `std::__cxx11::basic_string<char>`: those are completed through the
  incomplete→complete swap in `typecheck_compound_type`, so their inline
  members are parked in `deferred_typechecking` (not `deferred_method_bodies`)
  and are not reliably pulled in by the odr-use hook. Retiring the hook
  therefore requires first routing those members through the same lazy
  trigger; it remains follow-on.

- **Pre-existing, unrelated to Option B** (reproduced on the baseline by
  stashing the changed file): `std::string s = "ab"` fails C++20/23
  constructor *resolution* (`char[3]` → `basic_string`), and a C++20/23
  assessed and **kept**). Disabling `queue_deferred_methods_of_instance`
  makes `std::string` construction a no-op again (the string tests and
  dog-food probes fail). The lazy odr-use path does **not** subsume it for
  system-header *extern-template* instances such as
  `std::__cxx11::basic_string<char>`: those are completed through the
  incomplete→complete swap in `typecheck_compound_type`, so their inline
  members are parked in `deferred_typechecking` (not `deferred_method_bodies`)
  and are not reliably pulled in by the odr-use hook. Retiring the hook
  therefore requires first routing those members through the same lazy
  trigger; it remains follow-on.

- **Pre-existing, unrelated to Option B** (reproduced on the baseline by
  stashing the changed file): `std::string s = "ab"` fails C++20/23
  constructor *resolution* (`char[3]` → `basic_string`), and a C++20/23
  `std::string` BMC run can core-dump. Both are out of scope here.
