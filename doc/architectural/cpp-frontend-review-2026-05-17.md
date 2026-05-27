# C++ Front-End Review — 2026-05-17

## Scope

Cross-referenced review of the 98 remaining dog-food failures
(`scripts/dogfood_goto_cc.sh --expand` against `src/util/`)
after the lazy class-body elaboration work landed (Phases 1A,
2A, 3, 4, 4b plus Phase 2 audit sites 1+2).  Each failure
category traced to a single root cause, classified, and matched
against N5008.

| | |
|---|---|
| Baseline at session start | 14 OK_CLEAN / 5 OK_NOISY / 98 FAIL / 0 CRASH |
| cbmc-cpp regression suite | 675 / 0 / 83 — green |
| commits in PR #8878 over `tautschnig/cpp11-parser-rework-squashed` | 15 |

## Failure breakdown

A first-error-line histogram of the 98 failing files (root
causes, not cascading errors):

| count | first error | class | category |
|---|---|---|---|
| 62 | `member operator on unnamed/incomplete struct (typically from a failed template instantiation)` | architectural bug | A |
| 11 | `found no match for symbol 'swap', candidates are: ...` | latent bug | B |
| 4 + 2 | `instantiating 'std::optional'`/`'std::unordered_map'` cascade with `invalid implicit conversion from '<<type:>>' to 'bool'` | architectural gap | C |
| 3 | `range-based for requires an array type` | architectural gap | D |
| 3 | `symbol 'id' is unknown` (downstream of A) | symptom of A | A |
| 1 | `instantiating 'std::vector' with <size_t, struct allocator>` | external blocker | E |
| 1 | `instantiating 'std::unordered_set' with <struct exprt, ...>` | external blocker | E |
| 1 | `instantiating 'nfat' with <char>` | external blocker | E |
| 1 | `instantiating 'std::make_unique' with <struct nil>` | external blocker | E |
| 1 | `address_of error: '...' not an lvalue` | latent bug | F |
| 1 | `parse error before 'virtual bool __do_upcast ('` | parser gap | G |
| 1 | `parse error before 'const exprt & _length'` | parser gap | G |
| 1 | `'mallinfo' does not uniquely resolve` | overload-resolution | H |
| 1 | `'unique_ptr' candidates are: ...` (no match for direct-init) | latent bug | F |
| 1 | `'remove' candidates are: ...` (no match) | latent bug | F |
| 1 | `'read' is unknown` (downstream of A) | symptom of A | A |

The single biggest cluster (≈63%) is **Category A**: 62 files
all fail the same way — `expr.id() == ID_index`, `irep.hash()`,
`expr.is_not_nil()`, etc. — because `irept` (a base class
defined in `src/util/irep.h`) ends up in the symbol table as a
struct symbol with `ID_name` empty, `ID_tag` still a cpp_name
sub-tree, and zero registered components.  Section A below
explains the root cause.

## A. Class body abandoned because base-class elaboration throws

**N5008 reference**: [class.derived]/2 — "A class-or-decltype
shall denote a (possibly cv-qualified) class type that is not
an incompletely defined class".

**Mechanism (verified empirically by instrumenting
`typecheck_compound_body`)**:

1. `class irept` inherits from
   `non_sharing_treet<irept, std::map<irep_idt, irept>>`
   (or the `forward_list_as_mapt` variant).
2. `cpp_typecheckt::typecheck_compound_body` is entered for
   `tag-irept`.
3. **Before** `symbol.type.set(ID_name, symbol.name)` (line
   1215 of `cpp_typecheck_compound_type.cpp`), the function
   calls `typecheck_compound_bases(...)`.
4. `typecheck_compound_bases` resolves `non_sharing_treet<...>`
   which forces instantiation of `std::map<irep_idt, irept>`.
   That instantiation fails (libcxx's depth/structural limits).
5. The `throw 0` escapes `typecheck_compound_body` — line 1215
   never runs, the per-declarator try/catch in the body loop
   never starts.
6. The struct symbol is left with `body=present` (the parser
   already moved it under `ID_body`), `n_components=0`,
   `ID_name=""`, and `ID_tag` still a cpp_name sub-tree.

**Consequence**: every reference to a member of `irept` from a
sibling class goes through `cpp_typecheckt::typecheck_expr_member`,
which does `cpp_scopes.set_scope(struct_identifier)` with
`struct_identifier = type.get(ID_name) = ""`.  Pre-this PR
that was a SIGABRT (`id '' not found`); after `dd0dc0fcae`
it's the localized "member operator on unnamed/incomplete
struct" diagnostic.  62 of 117 files in `src/util/` reference
`irept` somewhere in their headers, so all 62 fail.

**Class**: architectural bug.

**Why my one-line attempt regressed**: I tried hoisting
`set(ID_name, symbol.name)` above `typecheck_compound_bases`
and wrapping the bases call in a top-level try/catch.  Result:
4 previously-OK files (`options.cpp`, `validate_expressions.cpp`,
`validate_types.cpp`, `xml_irep.cpp`) regressed, and
`ref_expr_set.cpp` flipped from FAIL to CRASH.  The naive
recovery exposes downstream code to a class with body=present,
ID_name set, but no inherited members — and that conflicts with
several existing assumptions about base-class members being
included in the components vector by the time consumers iterate
it (e.g. `cpp_typecheck_constructor.cpp`'s base copy/move
synthesis).

**Recommended re-architecture** (estimated 3–5 days of focused
work):

1. **Set `ID_name`/`ID_tag` to the resolved class name as the
   *first* thing `typecheck_compound_body` does**, before any
   sub-elaboration.  This is purely defensive and matches
   [class.name]/1 (the class name is in scope from the
   declarative-region of its definition).
2. **Track per-base-class failure separately from per-member
   failure.**  A throw from `typecheck_compound_bases` should
   leave the class registered with the inheritance edge marked
   "unresolved" (`ID_C_unresolved_base = id(failing_base)`)
   and continue with the body.
3. **Teach `cpp_typecheck_expr_member` to recognise classes
   with unresolved bases**: emit a focused "member of class
   with unresolved base X" error, not the generic "unnamed
   struct".  This makes diagnostics actionable.
4. **Teach `cpp_typecheck_constructor.cpp`'s copy/move
   synthesis to skip unresolved bases** rather than ICE on the
   missing components list.  Same for vtable construction in
   `cpp_typecheck_compound_type.cpp`'s virtual-table walk
   (~line 640).

The bookkeeping is similar to the existing
`ID_C_lazy_member_type` / `ID_lazy_type_source` mechanism but
applies to the inheritance edge rather than to a member; the
two systems can share the same SFINAE retry helper
(`try_resolve_lazy_type`).  This is the single highest-impact
fix for dog-food (62 of 98 failures).

## B. SFINAE-constrained `swap<T>(T&, T&)` not selected

11 files fail at gcc-13's `bits/move.h` line 189:

```cpp
template<typename _Tp>
inline typename enable_if<__and_<__not_<__is_tuple_like<_Tp>>,
                                 is_move_constructible<_Tp>,
                                 is_move_assignable<_Tp>>::value>::type
swap(_Tp& __a, _Tp& __b)
```

Called with `unsigned int *, unsigned int *`.  All three
`enable_if` conjuncts are trivially true for a pointer type, so
the substitution succeeds and the candidate is viable per
[over.match.viable]/3.  CBMC reports "found no match" with a
list of 27 other constrained `swap` overloads — the unrestricted
template is not in the viable set.

**N5008 reference**: [temp.deduct]/8 ([temp.deduct.general]/8) —
"If a substitution results in an invalid type or expression,
type deduction fails. […] Invalid types and expressions can
result in a deduction failure only in the immediate context of
the deduction substitution loci."

**Mechanism (hypothesised, not yet verified)**: the deduction
of `_Tp = unsigned int *` succeeds, but the substitution into
the `enable_if<...>::type` defaulted return type traverses
`__is_tuple_like`, `is_move_constructible`,
`is_move_assignable` — class templates whose primary
specialisations are themselves SFINAE-constrained.  Somewhere
in that chain a sub-substitution fails *outside* the immediate
context, gets converted to an error rather than a deduction
failure, and the candidate is silently dropped.

**Class**: latent bug.

**Recommended fix path**:

1. Add an instrumented unit test that exercises exactly this
   pattern (`swap<T*>` with `T = int`) in
   `regression/cbmc-cpp/`.
2. Trace which substitution layer trips out of the immediate
   context.  Likely candidates: the variable-template form
   `is_trivially_destructible_v<T>` (Section C below), or the
   alias-template chain inside `__and_`.
3. The existing `sfinae_contextt` (in `cpp_sfinae_context.h`)
   already wraps deduction.  The likely defect is a missing
   `sfinae_contextt` around one of the inner substitutions —
   a single-site fix once located.

## C. `is_trivially_destructible_v<T>` and other `_v` template variables

6+ files cascade through `instantiating 'std::optional' with
<struct exprt>` → `_Optional_base` → `is_trivially_destructible_v`
→ `invalid implicit conversion from '<<type:>>' to 'bool'`.

**N5008 reference**: [temp.variable] — variable templates were
added in C++14 ([temp.variable]/1), and the standard-library
`_v` traits ([meta.unary.cat], [meta.unary.prop]) are
`constexpr bool` variable templates that expand to constant
expressions of type `bool`.  The implicit conversion to `bool`
in a context like `_Optional_base`'s
`enable_if<is_trivially_destructible_v<_Tp>>::value` is just
the value-initialised constant being substituted.

**Symptom**: CBMC's substitution reaches the variable template
but the substituted value is reported as `<<type:>>` rather
than a constant `bool`.  The implicit conversion to `bool`
then fails because `<<type:>>` isn't an expression.

**Class**: architectural gap.  Variable templates are recorded
in `STANDARD_COVERAGE.md` as partially supported; the
substitution machinery still treats them like type aliases in
some paths.

**Recommended fix**: add a `cpp_typecheckt::resolve_variable_template`
that mirrors the type-alias resolution but produces a
`constant_exprt` (or `symbol_exprt` for non-`constexpr`
variables) of the underlying type, not a `type_exprt`.  Wire
it into `cpp_typecheck_resolve.cpp` at the same sites that
currently handle alias templates.  Estimated 2–3 days.

This is the single biggest blocker for dog-fooding C++17 code
in general — every `_v` trait and every C++17 fold/concept
emulation hits it.

## D. Range-based `for` over class types

3 files fail at:

```cpp
for(const auto &symbol_pair : symbol_table.symbols)  // std::map
for(auto &ch : src)                                  // std::string
for(auto &ch : to_escape)                            // std::string
```

CBMC reports "range-based for requires an array type".

**N5008 reference**: [stmt.ranged]/1 — the range-based for
statement is equivalent to:

```cpp
{
  init-statementopt
  auto &&range = for-range-initializer ;
  auto begin = begin-expr ;
  auto end = end-expr ;
  for ( ; begin != end ; ++begin ) {
    for-range-declaration = * begin ;
    statement
  }
}
```

with `begin-expr`/`end-expr` chosen by [stmt.ranged]/1.3:

- (1.3.1) array type → `range` and `range + N`
- (1.3.2) class type with member `begin`/`end` → `range.begin()`,
  `range.end()`
- (1.3.3) otherwise → ADL lookup of `begin(range)`,
  `end(range)`

CBMC's current implementation handles only (1.3.1).

**Class**: architectural gap.  This is a missing feature, not
a bug.

**Recommended fix**: extend the range-based-for desugaring in
`src/cpp/cpp_typecheck_code.cpp` (search for `range-based`).
For the class-with-member path the desugaring is straightforward
once we have a working `obj.begin()` overload set (which we
do).  ADL lookup of free `begin`/`end` is harder but rarely
needed for STL types whose containers expose member begin/end.
Estimated 2–3 days for (1.3.2), another 2 days for (1.3.3).

`src/util/run.cpp` and `src/util/string_utils.cpp` use this
over `std::string`; `src/util/get_module.cpp` over
`std::map<irep_idt, symbolt>`.  All three would compile cleanly
once (1.3.2) lands.

## E. Deep template instantiation cascades that won't resolve

Four single-file errors are libcxx-internal cascades:

- `std::vector<size_t, std::allocator<size_t>>` from
  `bits/stl_bvector.h:740`
- `std::unordered_set<exprt, irep_hash, equal_to, allocator>`
  from `src/util/ref_expr_set.h:20`
- `std::optional<interval_uniont>` from `src/util/interval_union.h:73`
- `nfat<char>` from `src/util/edit_distance.h:27`

All trace to either (a) [Category A] (a base class whose
elaboration throws cascades), (b) [Category C] (`_v` traits),
or (c) genuinely unsupported libcxx pattern (e.g.,
specialised-in-detail-namespace member function templates).

**Class**: external blocker — these are downstream consequences
of the architectural items above.  Fixing A and C should clear
most of these; the residue (genuinely unsupported libcxx
patterns) would need a separate libcxx-emulation effort that
the dog-food gate doesn't require.

## F. Overload resolution misses on direct-initialisation

Three files fail with "found no match for symbol X, candidates
are:" where the candidate listed is exactly the right one for
the call.  Examples:

- `unique_ptr<output_filet>` direct-init from a `output_filet*`
  in `src/util/output_file.cpp` line 29.
- `remove(...)` call ambiguity in `src/util/file_util.cpp`.
- "`address_of error: '<expr>' not an lvalue`" in
  `src/util/file_util.cpp` for what is actually a perfectly
  good lvalue.

**N5008 reference**: [over.match.copy] (12.2.2.6 in N5008) —
copy/direct initialisation overload resolution.  When the
target has class type T and the source is a single argument,
the candidate set is T's converting constructors and converting
conversion functions in the source's class.

**Class**: latent bug.  Each is likely an isolated defect
(parameter type mismatch, missing const-qualifier propagation,
or an initialiser-list quirk).

**Recommended fix path**: per-file diagnosis.  The total file
count is small enough (3) that there's no bulk pattern to fix;
each can be a focused bug-and-test.

## G. Parser gaps on declarators

Two files fail at parse:

- `parse error before 'virtual bool __do_upcast ('` — virtual
  function declarator with abstract specifier in a particular
  position.
- `parse error before 'const exprt & _length'` — const-ref
  parameter in some declarator position.

**N5008 reference**: [dcl.decl] — declarator grammar.

**Class**: parser gap.  Likely each is a single-rule LALR
miss in `src/cpp/parse.cpp`.

**Recommended fix path**: minimal reproducer per case, debug
the parse-tree builder.

## H. `mallinfo` ambiguity

A single file (`src/util/memory_info.cpp`) fails with
`'mallinfo' does not uniquely resolve`.  Two GCC versions of
`mallinfo` (the deprecated one and `mallinfo2`) shadow each
other.

**N5008 reference**: [basic.lookup.unqual] — name lookup must
resolve to a single declaration.

**Class**: latent bug — preprocessor macro conflict between
`<malloc.h>` system header and the user code.

**Recommended fix**: out of scope for the C++ front-end;
adjust user code or add a `--undef mallinfo` to the dog-food
goto-cc invocation.

## What would *not* be fixed by re-architecting

- The libcxx structural failures (Category E) — not all of them
  trace to A or C.  Some libcxx patterns (`__builtin_*` deep
  inside `<bits/...>`) genuinely require deeper compiler
  support that's beyond a "C++ front-end" remit.  Customers
  compiling their own code rarely hit these; they're an
  artifact of libcxx 13 internals.

- Some category F cases are the user's bug (`mallinfo`
  ambiguity in `src/util/memory_info.cpp` is debatable).

## Ranked recommendations

In order of cost-adjusted dog-food impact:

| rank | item | est | dog-food impact | risk |
|---|---|---|---|---|
| 1 | Category A: base-class elaboration recovery | 3–5 d | up to 62 → clean | medium |
| 2 | Category C: variable templates (`_v` traits) | 2–3 d | up to 6 → clean (and unblocks much C++17 customer code in general) | low |
| 3 | Category D.(1.3.2): range-based for over member begin/end | 2–3 d | 3 files; STL idioms generally | low |
| 4 | Category B: SFINAE viability for unrestricted templates | 1–2 d | 11 files | low (focused) |
| 5 | Category F/G/H: per-file diagnosis | 1 d each | 1 file each | low |

Working through ranks 1–4 in order would push the dog-food
gate from 14/5/98/0 toward 80+/?/<35/0, hitting the customer-
readiness target of ≥80% OK_CLEAN set in
`cpp-frontend-review.md` §8.

## What I would NOT do

- **Skip the architectural fix in Category A and try to handle
  it in `typecheck_expr_member` only.**  That just moves the
  diagnostic earlier; the underlying class is still in a
  half-broken state and consumers in
  `cpp_typecheck_constructor.cpp`,
  `cpp_typecheck_compound_type.cpp`'s virtual-table walk,
  `cpp_typecheck_function.cpp`'s base-method synthesis, and the
  resolver's class-scope traversal will all hit it differently.
  The right shape is what the lazy class-body work installed
  for class members: store enough information on the failure to
  let consumers either drive on-demand resolution or skip
  cleanly, and replicate that pattern at the inheritance edge.

- **Reach into libcxx headers and rewrite them.**  The lazy
  elaboration discipline has shown that libcxx structural
  failures don't propagate badly when the producer side is
  honest about what failed.  Going the other way — patching
  libcxx — creates a maintenance burden across libstdc++,
  libc++, MSVC STL, and historic GCC versions that customers
  may use.

## 2026-05-18 follow-up: Category A is gated on Category C

After committing the Category A step 1 fix (`a65e4b4362`,
hoisting `set(ID_name, symbol.name)` above
`typecheck_compound_bases` so the class name is visible even
when base elaboration throws), an attempt at the full Category
A recovery — wrapping the substitution-prone calls in
`typecheck_compound_bases` (`resolve` and
`elaborate_class_template`) in a top-level try/catch so a
failed base just sets the inheritance edge to nil and lets the
body continue — empirically REGRESSED dog-food from 14/5/98/0
to 11/4/102/0 by exposing four previously-OK files
(`options.cpp`, `validate_expressions.cpp`, `validate_types.cpp`,
`xml_irep.cpp`) to a class with body=present, ID_name set, but
inherited typedefs missing.

The specific failure mode in `irep.h` is illuminating:

```cpp
class irept : public non_sharing_treet<irept, std::map<...>>
{
public:
  using baset = tree_implementationt;   // ← fails: inherited typedef
                                        //   from the failed base
  ...
};
```

When base elaboration is recovered (so the class body is
processed), the very first member-typedef `using baset =
tree_implementationt;` references `tree_implementationt`, an
inherited typedef from the failed base.  The lookup throws,
the class body is again abandoned, and the symbol's state is
worse than before (more partial registrations expose
downstream consumers to inconsistent state).

**Trace of the underlying failure**: the `std::map<irep_idt,
irept>` instantiation fails at:

```
instantiating 'std::optional' with <struct basic_string>
  → 'std::_Optional_base' with <struct basic_string, TRUE, TRUE>
    → 'std::is_trivially_destructible_v' with <struct basic_string>
      → ...
        → invalid implicit conversion from '<<type:>>' to 'bool'
```

The variable-template instance `is_trivially_destructible_v<T>`
returns a `symbol_exprt` whose type-irep has empty `id()` (so
`expr2c.cpp` prints it as `<<type:>>`).  Substituting it where
`bool` is expected (in another `enable_if` chain) trips
`implicit_typecast_helper`'s validator.

**This means Category A's full fix is gated on Category C.**
Until variable-template `_v` traits evaluate cleanly, fixing
the base-elaboration cascade in isolation just shifts the
failure into the body of the affected class.

**Revised priority ordering** (compared to the table at the
top of this document):

| rank | item | est | dog-food impact | risk |
|---|---|---|---|---|
| 1 | **C: variable templates (`_v` traits)** | 2-4 d | 6 + unblocks A | low |
| 2 | A: base-class elaboration recovery (full) | 2-3 d AFTER C | up to 62 → clean | medium |
| 2 (also) | A step 1: `set(ID_name)` hoist | DONE (`a65e4b4362`) | diagnostic improvement | none |
| 3 | D: range-based for over member begin/end | 2-3 d | 3 + STL idioms | low |
| 4 | B: SFINAE viability for unrestricted templates | 1-2 d | 11 files | low |
| 5 | F/G/H: per-file diagnosis | 1 d each | 1 file each | low |

The change of ordering is the architectural lesson from
2026-05-18: the Category A *symptom* (62 files with "unnamed
struct" / now "specific member unknown" diagnostics) is real,
but Category C is the mechanical CAUSE.  Fix C and most of A
clears with it.

## 2026-05-19 follow-up: Category C is mostly a warning, not a blocker

The 2026-05-18 finding was that "Category A is gated on Category C
(variable template `_v` traits)".  Today's investigation flips that
conclusion: **Category C as defined is largely a benign warning,
not the dog-food blocker it was thought to be.**

**Empirical trace of `is_trivially_destructible_v<basic_string>`**:

1. The variable-template instantiator returns a `symbolt` whose
   `value.id` is `cpp_name` (the unresolved expression
   `is_trivially_destructible<basic_string>::value`) and whose
   `value.is_constant` is false.
2. That value is consumed as a non-type template argument in
   `_Optional_base<basic_string, X, Y>`.
3. Inside `cpp_typecheck_conversions.cpp::implicit_typecast_helper`,
   the converter sees the cpp_name with empty `e.type().id()` and
   target type `c_bool`.
4. The pre-existing "downgrade to non-fatal when the target type is
   malformed" branch issues a *warning* ("invalid implicit
   conversion from '<<type:>>' to 'bool'"), inserts a
   `typecast_exprt`, and returns.
5. Compilation continues.  The optional<basic_string> template
   instance is registered.

**Of the 5 dog-food OK_NOISY files, only 1 (`xml_irep.cpp`) emits
the variable-template warning.** The other four
(`help_formatter.cpp`, `signal_catcher.cpp`, `string2int.cpp`,
`union_find.cpp`) emit Category B (`found no match for 'swap'` /
`'invariant_violated_string'`) misses.

**Of the dog-food FAIL files**, only six emit the variable-template
warning at all:

```
src/util/cmdline.cpp           WARN=1 ERR=2 GB=no
src/util/expr_initializer.cpp  WARN=3 ERR=6 GB=no
src/util/interval_union.cpp    WARN=2 ERR=4 GB=no
src/util/parse_options.cpp     WARN=1 ERR=2 GB=no
src/util/xml.cpp               WARN=1 ERR=1 GB=no
src/util/xml_irep.cpp          WARN=1 ERR=1 GB=yes
```

In each case the *errors* trace to other root causes:

* `cmdline.cpp` fails at `symbol 'value_or' is unknown` — a
  member-function-template (`std::optional<T>::value_or<U>`) lookup
  miss.  The class is registered, but its template-method
  declarations didn't propagate into the instantiated class scope.
  This is a Category A-deep issue (partial registration of class
  members).
* `expr_initializer.cpp` and `interval_union.cpp` fail at
  `bad assignment operator 'assign_mod'` in `bigint.hh:308` —
  CBMC's compound-assignment-operator handling for `BigInt operator%`.
  Unrelated to variable templates.
* The remaining files fail with similar downstream issues.

**The "deep" Category C fix would be**: when the resolver hands back
a variable-template instance with `value.id == ID_cpp_name`, drive
`typecheck_expr` on the value to resolve the qualified
class-member-access (`Class<T>::value`).  An attempt at this fix
showed:

* `typecheck_expr` *throws* on the cpp_name silently because it
  cannot follow the inheritance chain.  In libstdc++,
  `is_trivially_destructible<T>::value` is inherited from
  `__and_<__is_destructible_safe<T>, __bool_constant<__has_trivial_destructor(T)>>::type`,
  itself a metafunction-typedef.  CBMC's qualified-name lookup at
  the instantiation point doesn't follow `::type`-metafunction
  bases recursively.

The real architectural item is **multi-level template inheritance
with `::type` metafunction bases** — the same pattern shows up in
many libstdc++ traits.  Fixing that probably involves making the
resolver follow `typename Base::type` recursively when looking up
inherited static members.  This is genuinely 3–5 days of focused
work and is what Category C should have been re-named to.

**Revised Category C definition**: "qualified-name lookup of an
inherited static member through a chain of `::type` metafunction
bases".

**Revised priority** (this is the fourth iteration of the table —
the symptom-based ranking has been misleading throughout, and each
session has refined the actual lever):

| rank | item | est | dog-food impact | risk |
|---|---|---|---|---|
| 1 | A-deep: partial class registration (member-function templates not propagating into instantiated class scope) | 5-7 d | 62+ files | high |
| 2 | D: range-based for over member begin/end | 2-3 d | 3 + STL idioms | low |
| 3 | B: SFINAE viability for unrestricted `swap<T*>` | 1-2 d | 11 files | low |
| 4 | C-revised: multi-level metafunction inheritance lookup | 3-5 d | unblocks A-deep partly | medium |
| 5 | A step 1 (set ID_name hoist) — DONE (`a65e4b4362`) | done | diagnostic improvement | none |
| 6 | F/G/H: per-file diagnosis | 1 d each | 1 file each | low |

The architectural lesson from May 17 → 18 → 19 is that the
dog-food failure cascade has THREE distinct root causes that the
symptom histogram doesn't separate:

1. **Architectural ordering** (Category A step 1, FIXED): class
   names must be in scope before sub-elaboration.
2. **Member-template registration** (newly identified A-deep):
   when a class template is instantiated, its template member
   functions need to register in the instantiated class's scope.
   Currently they don't, and consumers see "symbol X is unknown"
   for valid class members.
3. **Multi-level metafunction lookup** (revised Category C):
   `Class<T>::inherited_value` where `inherited_value` traverses
   multiple `::type` typedefs requires the resolver to follow
   metafunction-typedef bases.

The original 2026-05-17 review's symptom-based table conflated
these.  The 2026-05-18 attempt at base-class recovery hit issue
(2) and (3) cascading in the body of `irept`.  The 2026-05-19
attempt at variable-template fixing showed (3) is a deep
architectural issue beyond a single-session fix.

**No code changes today.**  Dog-food unchanged at 14/5/98/0.
The review's priority table is updated to reflect the lessons.

## 2026-05-22 Category B investigation

The dog-food failure category labelled "B: SFINAE viability for
unrestricted `swap<T*>`" turns out to have two separate root
causes, not one.  Today's investigation found and fixed one
(latent-bug); the other (architectural) is a deeper deduction
issue that triggers only when `<ios>` (or its transitive
includers `<sstream>`, `<iostream>`) is in scope.

### Latent bug: `ID_assign_mod` missing from operator-overload switch

`bigint.hh:308`'s `inline BigInt operator% (...) { return BigInt(lhs) %= rhs; }`
trips on `BigInt::operator%=` overload resolution.  The switch
in `cpp_typecheckt::typecheck_side_effect_assignment` mapping
the statement id to an operator name handled all compound
assignments EXCEPT `%=` (`ID_assign_mod`).  Any non-POD class
type using `%=` would emit "bad assignment operator
'assign_mod'" and abort.

Fixed in commit `9ef2f87307`.  Regression test
`regression/cbmc-cpp/cpp_compound_assign_mod` covers it.
13 dog-food files (`algebraic_number.cpp`, `arith_tools.cpp`,
`bv_arithmetic.cpp`, `config.cpp`, `expr.cpp`,
`expr_initializer.cpp`, `fixedbv.cpp`, `ieee_float.cpp`,
`interval_constraint.cpp`, `interval_union.cpp`,
`lower_byte_operators.cpp`, `mp_arith.cpp`, `rational.cpp`)
no longer hit this error, but each surfaces a downstream
issue (operator< on BigInt not finding the user-defined free
overload, the `swap` deduction issue below, etc.) so the
totals don't change.

### Architectural issue: `<ios>` poisons template deduction for swap

Empirical bisection:

| header included | swap on `unsigned int *` |
|---|---|
| `<utility>` only | ✓ works |
| `<vector>` | ✓ works |
| `<string>` | ✓ works |
| `<tuple>` | ✓ works |
| `<optional>` | ✓ works |
| `<unordered_map>` | ✓ works |
| `<iosfwd>` | ✓ works |
| `<ios>` | ✗ "found no match for symbol 'swap'" |
| `<streambuf>`, `<iostream>`, `<istream>`, `<ostream>`, `<locale>`, `<sstream>` | ✗ same |

With `<ios>` in scope, `cpp_typecheck_resolvet::guess_function_template_args`
returns `nil_exprt()` for ALL 13 swap template candidates,
including move.h:189's unrestricted `swap<_Tp>(_Tp&, _Tp&)`
that should match `unsigned int *`.  Without `<ios>`, the same
candidate succeeds.

Without further deep tracing, the most likely cause is that
including `<ios>` brings in template-class specialisations
(or registered scopes) that pollute `template_map` state or
make some intermediate substitution fail during the SFINAE
return-type check (specifically `enable_if<__and_<...>::value>::type`
where the chain has to evaluate `is_move_constructible<unsigned int *>::value`
through multi-level inheritance).

This is the same family as the **C-revised** issue in this
review (multi-level metafunction inheritance lookup).  The
underlying lever is the same: `Class<T>::value` lookup needs
to traverse `typename Base::type` typedef bases.

### Why the dog-food count didn't move

Both Category B sub-issues are present in the 13 files that
were attributed to "B".  Fixing one (`assign_mod`) just
exposes the other (`swap` deduction).  Fixing the deduction
would need the C-revised work — they share the same lever.

### Revised priority (5th iteration)

| rank | item | est | status |
|---|---|---|---|
| 1 | A-deep: member-function-template registration | 5-7 d | unstarted |
| 2 | C-revised: multi-level metafunction inheritance | 3-5 d | this would unblock B's deduction issue too |
| 3 | D: range-based for over member begin/end | 2-3 d | DONE (`1363eeaaca`) |
| 4 | A step 1: `set(ID_name)` hoist | done | DONE (`a65e4b4362`) |
| 5 | B-bug: `ID_assign_mod` operator overload | done | DONE (`9ef2f87307`) |
| 6 | B-arch: deduction with `<ios>` poisoned scope | 3-5 d | downstream of C-revised |
| 7 | F/G/H per-file | 1 d each | unstarted |

Concrete recommendation for the next session: **Category C-revised**
(multi-level metafunction inheritance lookup) is now identified as
the real lever — it would unblock both the `_v` trait warnings AND
the `<ios>`-poisoned swap deduction.  A-deep remains the largest
single dog-food unblock but is high-risk; C-revised is medium-risk
with broad reach (B-arch and many libstdc++-internal traits).

## 2026-05-22 Category C-revised investigation

Goal: implement multi-level metafunction inheritance lookup so
SFINAE chains of the form
`enable_if<__and_<...>::value>::type` can resolve cleanly when
the inner `::value` is inherited from a base class via
`typename Base::type` chains.

### Where exactly the throw happens

Empirical tracing in
`cpp_typecheck_resolvet::guess_function_template_args`
identifies the failure point: line ~5437 (catch block after
`cpp_typecheck.typecheck_type(function_type)`).  The `function_type`
after substitution has `id == ID_code` and
`return_type().id() == ID_cpp_name`.  When `typecheck_type`
processes that return type, evaluating the inherited `::value`
through the `__and_<...>::type` chain throws.  The catch
silently drops the candidate per [temp.deduct]/8 SFINAE.

Trace from the dog-food repro (
`exception_ptr` swap + `<string>` + `std::swap(unsigned int *, …)`):
4 distinct `swap<Type0>` candidates fail at this catch:

1. The `_Require<...>` C++20 concept-style swap (alias).
2. The unconstrained `enable_if<__and_<__not_<__is_tuple_like<_Tp>>,
   is_move_constructible<_Tp>, is_move_assignable<_Tp>>::value>::type`
   from `bits/move.h:189` — the one that should match
   `unsigned int *`.
3-4. Tuple swap variants with `enable_if<__and_<...>::value>::type`.

After `_Tp = unsigned int *` substitution, the return type is
`enable_if<__and_<__not_<__is_tuple_like<unsigned int *>>,
is_move_constructible<unsigned int *>,
is_move_assignable<unsigned int *>>::value>::type`.
Static-asserting that exact `__and_<...>::value` evaluates to
`true` for `unsigned int *` works (verified at user-side).
But during *deduction substitution*, the same evaluation
throws.

### Why the obvious targeted fix doesn't work

Tried: in the catch block, when the return type is a SFINAE-
shaped `cpp_name`, fall back to `void` (keeping the candidate
viable).  The minimal swap test still failed — when
substitution throws, the return type stored in the
`function_type` is not the rich SFINAE-shaped cpp_name we'd
look for.  Empirical trace:
`ret.id=cpp_name sub_count=0 named_sub_count=0`.  The cpp_name
appears to have been "shelled" by partial substitution before
the throw, leaving no detectable shape we can pattern-match
against.

### Why user-side reproductions all pass

Multiple user-side reproductions of the SFINAE chain
(including 4-level metafunction inheritance, `__and_<>`
variants, and the exact libcxx pattern) all pass cleanly in
CBMC.  This suggests the failure is not in the SFINAE
machinery itself but in some *symbol-table* / *template_map*
state that builds up only in libcxx's deeply-included context
(specifically:
`<bits/exception_ptr.h>` ∪ `<bits/basic_string.h>` triggers
the failure but each alone works).

The bisection narrowed it to: when both
`std::__exception_ptr::swap(exception_ptr&, exception_ptr&)`
(brought into `std::` via `using __exception_ptr::swap`) AND
the `swap` template family (move.h:189 + basic_string.h's
template + tuple/array/etc. specializations) coexist, **all
swap template deductions silently fail**, even for argument
types that should be trivially compatible.

### Conclusion: this is a multi-day item, not a single-session fix

Both candidate fix paths require deeper rework:

1. **Targeted: relax the substitution-failure catch when the
   thrown expression carries the substitution-failure shape.**
   Doesn't work as observed because the thrown state doesn't
   preserve the shape.  Would need to instrument the
   substitution path at a deeper level — capture the exact
   substitution failure reason from inside the typecheck_type
   call, not from the post-throw inspection.

2. **Architectural: implement multi-level metafunction
   inheritance lookup.**  When evaluating
   `Class<T>::value` and `value` is inherited via `typename
   Base::type` chains, walk the inheritance recursively and
   evaluate inherited static members.  This is the proper fix
   per N5008 [class.member.lookup] and would correctly evaluate
   `__and_<...>::value` to `true` rather than throwing.

Both are 3-5 days of careful work.  Today's investigation
confirms the diagnosis but stops short of landing a fix.

### Final priority (6th iteration)

| rank | item | est | status |
|---|---|---|---|
| 1 | A-deep: member-function-template registration | 5-7 d | unstarted |
| 2 | C-revised: multi-level metafunction lookup | 3-5 d | diagnosis confirmed; not landed |
| 3 | D: range-based for over member begin/end | done | DONE (`1363eeaaca`) |
| 4 | A step 1: `set(ID_name)` hoist | done | DONE (`a65e4b4362`) |
| 5 | B-bug: `ID_assign_mod` operator overload | done | DONE (`9ef2f87307`) |
| 6 | B-arch: deduction with `<ios>` in scope | downstream of C-revised | (this section) |
| 7 | F/G/H per-file | 1 d each | unstarted |

The architectural lever for both Category B-arch and Category
C-revised is the same: make CBMC's class-member-access lookup
follow `typename Base::type` typedef chains during template
substitution.  This unblocks the `_v` traits AND the
`<ios>`-poisoned swap deduction in one piece of work.

This is the recommended next focused effort, with realistic
3-5 days of scope.  A-deep remains the largest single dog-food
unblock but at higher risk.  Both should be tackled in
dedicated focused sessions, not interleaved with other work.

## 2026-05-22 Group 2 investigation — invariant_violated_string failures share root cause with B-arch/C-revised

After Category A-deep step 1 landed (`c050302afe`), the
dominant residual dog-food cluster (15/22/80/0) is 30 files
failing at the first PRECONDITION call inside libstdc++'s
`basic_string::sharing_treet` constructor:

```
src/util/irep.h:177:1: error: found no match for symbol
  'invariant_violated_string', candidates are:
  symbol void ...
  (const struct basic_string &, const struct basic_string &,
   const signed int, const struct basic_string &,
   const struct basic_string &) ...
argument types:
  char [16l]  char [14l]  signed int  char [21l]  char [13l]
```

The argument types `char[N]` should convert to `const std::string &`
via the standard implicit user-defined conversion sequence:

1. `char[N] → const char *`  ([conv.array])
2. `const char * → std::string`  via converting constructor
3. bind to `const std::string &`  ([dcl.init.ref])

### Bug localized

Tracing `user_defined_conversion_sequence` for
`char[N] → basic_string<char>`:

* `basic_string<char>` has 189 components, including 7
  constructors with various signatures.
* The 4-param converting ctor
  `basic_string(const _CharT*, size_type, const _Alloc& = _Alloc())`
  is registered with sig
  `[pointer, &pointer, unsignedbv, &pointer(default)]`.
  Param 2 (size_type) has no default, so
  `all_extras_have_default = false` and the candidate is
  skipped.
* The 3-param converting ctor
  `basic_string(const _CharT*, const _Alloc& = _Alloc())` is
  **not registered as a non-template constructor** at all.
  It would have shape `[pointer, &pointer, &pointer(default)]`
  — that signature is missing from CBMC's components list for
  `basic_string<char>`.

Why is the 3-param converting ctor missing?  Look at libstdc++:

```cpp
#if __cpp_deduction_guides && ! defined _GLIBCXX_DEFINING_STRING_INSTANTIATIONS
      // 3076. basic_string CTAD ambiguity
      template<typename = _RequireAllocator<_Alloc>>
#endif
      _GLIBCXX20_CONSTEXPR
      basic_string(const _CharT* __s, const _Alloc& __a = _Alloc())
```

In C++17 mode, the converting ctor is wrapped by a defaulted
template parameter
`template<typename = _RequireAllocator<_Alloc>>`.  That makes
the ctor a **function template**, not a regular member
function.  CBMC's `user_defined_conversion_sequence` does
iterate template ctors via the
`has_template_constructor` fallback (in
`cpp_typecheck_conversions.cpp:1709`), which calls
`new_temporary` → `cpp_constructor` → ctor overload resolution
including template ctors.

Empirical trace: that fallback is reached **59 times** for
`char[] → basic_string<char>` in a single dog-food compile.
**All 59 calls throw** during `guess_function_template_args`'s
substitution.

### Same root cause as Category B-arch / C-revised

`_RequireAllocator<_Alloc>` is defined in libstdc++ as

```cpp
template<typename _Alloc>
  using _RequireAllocator
    = typename enable_if<__is_allocator<_Alloc>::value, _Alloc>::type;
```

This is **exactly the same SFINAE pattern** as the C-revised
swap deduction:
`enable_if<__and_<__not_<__is_tuple_like<T>>,
                 is_move_constructible<T>,
                 is_move_assignable<T>>::value>::type`.

CBMC's `cpp_typecheck.typecheck_type(function_type)` (in
`guess_function_template_args` at line ~5432) cannot evaluate
`__is_allocator<_Alloc>::value` and throws.  The catch block
treats this as deduction failure → the candidate is dropped →
no converting ctor is found → "found no match" cascade.

So **Group 1 (36 files: swap + sharing_treet + __and_) and
Group 2 (30 files: invariant_violated_string) share a single
root cause**: SFINAE substitution failing during template
function/constructor deduction because CBMC cannot evaluate
libstdc++'s trait wrapper class templates.

That's **66 of 80 dog-food failures (82%)** with ONE
architectural fix.

### Recommended fix paths (3-5 day items)

#### Path 1: Trait intrinsic emulation (least invasive, most
focused)

Recognise specific libstdc++ trait class templates by
qualified name and short-circuit their evaluation to known
constants:

* `__is_allocator<allocator<T>>::value` → `true`
* `__is_allocator<X>::value` for non-allocator X → `false`
* `is_move_constructible<T>::value` →
  `__is_constructible(T, T&&)` (CBMC's existing builtin)
* `is_move_assignable<T>::value` →
  `__is_assignable(T&, T&&)` (CBMC's existing builtin)
* `__is_tuple_like<T>::value` for scalar/pointer T → `false`
* `__not_<X>::value` → `!X::value`
* `__and_<X, Y, ...>::value` → AND of values
* `__or_<X, Y, ...>::value` → OR of values
* `enable_if<true, T>::type` → `T`
* `enable_if<false, T>::type` → throws (no member)
* `_RequireAllocator<X>` (alias) → expand inline
* `_RequireNotAllocator<X>` → expand inline

CBMC already has builtin `__is_constructible` and
`__is_assignable` (at `cpp_typecheck_expr.cpp:211`).  The new
work is to recognise the libstdc++ wrappers and route them
to those builtins.

Intercept point: `instantiate_template` for class templates
matching the known trait names — bypass the standard
substitution, build the result directly.

Estimated 3-5 days, unblocks 66 of 80 dog-food failures.

#### Path 2: Architectural multi-level metafunction lookup (5-7 days)

Implement proper `Class<T>::value` lookup that walks
inherited static members through `typename Base::type`
typedef chains per [class.member.lookup].  This is the
correct fix per the standard but requires deeper rework of
`cpp_typecheck_resolve.cpp`.

#### Path 3: Permissive substitution catch (1-2 days, may be unsafe)

In `guess_function_template_args`'s substitution catch block,
when the throw came from a defaulted template parameter that
is a SFINAE alias, ASSUME the deduction succeeds and
continue with the function-arg deduction.  Empirically it
should usually be true; if false, downstream type-check will
catch the mismatch.

This was tried at the C-revised level for the function
return type and didn't work because the cpp_name had been
"shelled" by partial substitution.  Worth re-trying at the
defaulted-template-parameter level specifically.

### State at end of session

* Investigation: complete.  Bug localized.  Group 2 = same
  root cause as Group 1.
* Fix: not landed.  All paths require multi-day focused work
  outside this session's budget.
* No code changes from this investigation; instrumentation
  reverted, working tree clean.

Recommended next session: pursue Path 1 (trait intrinsic
emulation) as a 3-5 day focused project.  This is the
single highest-leverage architectural fix remaining for
dog-food unblocking — 66 of 80 failures (82%).

## 2026-05-22 Trait intrinsic emulation attempt — diagnostic-only change landed; full emulation deferred

### What landed

`__is_base_of: accept struct types, not only class types` (commit
`43fa4ecfe7`).  Two corrections to CBMC's existing
`__is_base_of` builtin that were exposed during Group 2
investigation and are independently standard-conforming:

1. **Use `to_struct_type` instead of `to_class_type`.**  Per
   N5008 [class]/1, the `class` and `struct` keywords differ
   only in default member access — both produce class types
   for inheritance purposes.  CBMC stored `struct` declarations
   as `struct_typet` without `ID_C_class`; the
   `to_class_type` cast preconditioned on `ID_C_class` and so
   crashed on user code where `struct B {}; struct D : B {};`
   was passed to `std::is_base_of`.
2. **Self-base check.**  Per N5008 [meta.rel] table:
   `is_base_of<T, T>::value` is true for any class type T
   (a class is a base of itself for the purpose of this trait,
   per the Cpp17BaseOfRequirement).  CBMC's `has_base` only
   walked actual bases.

Regression test `cpp17_is_base_of_struct` exercises both
fixes.

### Diagnostic side-effect

The self-base fix correctly makes `is_base_of<X, X>::value`
return true.  3 dog-food files (`run.cpp`, `console.cpp`,
`irep_ids.cpp`) move from OK_CLEAN to OK_NOISY because the
SFINAE-gated function template
`invariant_violated_structured<ET, ...>` now goes through
deduction (its return-type SFINAE
`enable_if<is_base_of<invariant_failedt, ET>::value>::type`
correctly succeeds for `ET = invariant_failedt`).  The
function-template body's instantiation then fails downstream
with one context message.  The files still produce valid goto
binaries — only the diagnostic-cleanliness count regresses.

This is a strictly conforming improvement: the code now
matches normative behavior.  The downstream instantiation
failure is a pre-existing, separate issue (parameter pack
expansion in `invariant_violated_structured`'s body) that
SFINAE was previously masking.

### Trait intrinsic emulation — attempted, reverted

Tried implementing intrinsic emulation for the four
[meta.unary.prop] referenceable traits in `instantiate_template`:

* `is_move_constructible<T>` → routed to `__is_constructible(T, T&&)`
* `is_copy_constructible<T>` → `__is_constructible(T, const T&)`
* `is_move_assignable<T>` → `__is_assignable(T&, T&&)`
* `is_copy_assignable<T>` → `__is_assignable(T&, const T&)`

Approach: at top of `instantiate_template`, recognize known
trait class templates by qualified name; synthesize a struct
symbol with one static constexpr bool `value` member set via
the existing CBMC builtins; return early.

**Result**: 8 new dog-food crashes, 3 fewer OK_CLEAN, only -3
FAIL.  Net regression.

**Root cause of the regression**: my synthesized struct has
ONLY `value` as a member.  libstdc++'s `is_move_constructible`
inherits from `integral_constant<bool, V>`, which provides
`value`, `value_type` typedef, `type` typedef
(self-reference), `operator value_type()`, and
`operator()()`.  Downstream code (e.g.,
`__and_<...>::value` evaluation, structural metafunction
matching) accesses these other members.  When my synth
shadows the libstdc++ definition with a partial struct, those
accesses fail.

**Two correct paths forward** (both 2-3 days):

1. **Synthesize the FULL `integral_constant<bool, V>`
   interface.**  Build the struct with `value`, `value_type`,
   `type`, the conversion operator, and the call operator —
   either by inheriting from `std::integral_constant<bool, V>`
   directly (via a synthesised base) or by replicating its
   members.  The synthesized struct must look indistinguishable
   from a properly elaborated libstdc++ `is_move_constructible`
   to all downstream consumers.

2. **Intercept at resolve time, not instantiate time.**
   Instead of synthesising a class symbol, intercept at
   `cpp_typecheck_resolvet::resolve` when the cpp_name has the
   shape `Class<args>::value` and `Class` is a known trait.
   Return the boolean constant directly, never instantiating
   the class.  Doesn't conflict with libstdc++'s class
   definition.  Disadvantages: doesn't help cases that need
   `Class<args>::type` or the conversion operator.

Path 2 is simpler but partial; Path 1 is fuller-fidelity but
more code.  Either is the next focused multi-day effort.

### Empirical state at end of session

* dog-food: 12 OK_CLEAN / 25 OK_NOISY / 80 FAIL / 0 CRASH
  (vs baseline 15/22/80/0 — 3 files moved OK_CLEAN→OK_NOISY
  due to `is_base_of` standard-conforming fix exposing
  downstream pre-existing diagnostic; net same total useful
  outputs).
* regressions: 675/0/83 — all green.
* 28 commits ahead of pushed `ef662777b0`.

## 2026-05-22 Trait intrinsic emulation, attempt 2 — full integral_constant interface, also reverted

Following the user's directive to make the trait emulation
**correct and complete per the standard**, I implemented Option
1 from the previous iteration: synthesise the FULL
`integral_constant<bool, V>` interface per N5008 [meta.help].
The synthesised struct included:

* `static constexpr bool value` — the actual constant
* `using value_type = bool` — typedef
* `using type = <self>` — self-typedef
* (deferred) `operator bool()` and `operator()()` — needed by
  [meta.help] but not by the dog-food failure paths

The implementation also routes the value computation through
CBMC's existing `__is_constructible` / `__is_assignable`
builtins, which are exactly the normative definition per
[meta.unary.prop] table:

* `is_move_constructible<T>::value` == `__is_constructible(T, T&&)`
* `is_copy_constructible<T>::value` == `__is_constructible(T, const T&)`
* `is_move_assignable<T>::value`    == `__is_assignable(T&, T&&)`
* `is_copy_assignable<T>::value`    == `__is_assignable(T&, const T&)`

with proper [dcl.ref]/6 reference-collapsing applied so
`is_move_constructible<T&>` doesn't pass `T&&&` into the
builtin.

### Result

`imc20` and `imc_full` user-side tests pass cleanly with full
integral_constant interface (value, value_type, type
typedefs all accessible via the synthesised class).

But the existing regression test `cpp11_vector_size` fails:
`std::vector<int>::push_back(42)` no longer increments size,
and downstream `_M_impl._M_finish` pointer-arithmetic checks
fire as UNKNOWN/FAILURE.  Dog-food drops to 9/27/81/0 from
the 12/25/80/0 baseline.

### Why even the "complete" emulation regresses

The synthesis I implemented is **structurally complete** —
every field libstdc++'s `integral_constant<bool, V>` exposes
is present.  Yet vector behaviour changes.  Investigation
points to two contributing causes:

1. **My synth runs eagerly at the top of
   `instantiate_template`, before libstdc++'s normal
   elaboration.**  The synth inserts the symbol into
   `symbol_table`; when libstdc++'s `<type_traits>` code is
   later parsed and tries to elaborate the same class, the
   `if(symbol_table.has_symbol(...))` early-out makes the
   synth win.  The actual class libstdc++ would have
   elaborated has additional libstdc++-internal members (for
   example, the `_S_use_relocate` static probe or the
   inheritance from `__bool_constant` / `integral_constant`
   directly).  Those are absent in my synth.  Library code
   that dispatches on these *internal* members (via SFINAE
   on `_S_use_relocate` or via `is_base_of<bool_constant<X>,
   trait>`) takes a different path → vector ends up using
   the no-op default branch.

2. **I removed `is_macro = true` from the synthesised
   `value` symbol** to make pointer-to-member-data ADL work,
   but that means `value` is no longer a compile-time
   constant in CBMC's view.  Some libstdc++ paths
   `static_assert` on `is_X<T>::value`; the assertion
   becomes a non-compile-time evaluation and dispatches
   change.

### What "correct AND complete" actually requires

The N5008 [meta.unary.prop] semantic equivalence is correct
— routing through `__is_constructible` produces the
standard-required value.  But matching libstdc++'s
**implementation-defined internal layout** (which other
libstdc++ code reads via ADL / SFINAE on internal members)
is something else, and depends on:

1. **Full `integral_constant<bool, V>` interface**, including
   the conversion operator and call operator with proper
   constexpr code-typed bodies.
2. **Inheritance from a libstdc++-elaborated
   `integral_constant<bool, V>`**, so `is_base_of<...>` checks
   against the trait result give the same answer as the real
   libstdc++ trait.
3. **Synthesis only when libstdc++ elaboration would FAIL**,
   never as a replacement for a working libstdc++ class.
   This is harder to detect cleanly: the failure manifests
   as an unresolved `::value` after class-body processing,
   not as a throw, so the "fallback" hook needs to inspect
   the post-elaboration class.

That third constraint is the real blocker.  The synth-as-
replacement approach (this attempt) is structurally simpler
but conflicts with the libstdc++-internal layout dependence.
The synth-as-fallback approach requires inspecting the
class AFTER libstdc++ elaboration completes, detecting an
incomplete `::value`, and patching it up.  More invasive but
surgical.

### State at end of session

* `__is_base_of` fix landed (`43fa4ecfe7`) — strictly
  conforming improvement; produces 3 noisy-but-correct
  outputs that were previously OK_CLEAN due to silently
  failing SFINAE.
* Trait emulation infrastructure written and reverted.
  Available as documentation / future starting point.
* dog-food: 12/25/80/0 (vs baseline 15/22/80/0 — 3 files
  moved OK_CLEAN→OK_NOISY due to `is_base_of` standard
  conformance).
* regressions: 675/0/83 — all pass.
* 30 commits ahead of pushed `ef662777b0`.

### Recommended next session

The trait emulation needs a **synth-as-fallback** approach,
not synth-as-replacement.  Concretely:

1. Let libstdc++ elaborate the class normally.
2. After elaboration, if the class is one of the recognised
   traits AND its `::value` static member has no constant
   initializer (still nil or symbolic), patch in the
   computed value.
3. This preserves libstdc++'s internal layout while fixing
   the only thing CBMC couldn't compute (the SFINAE
   condition that bottoms out at `__is_constructible` /
   `__is_assignable` builtins).

Estimated 2-3 days; significantly safer than synth-as-
replacement.

## Status of this PR

15 commits ahead of pushed `ef662777b0`, all behaviour-change
gated:

- Pre-session: clang-format, libcxx test fixes, scanner fix,
  Phase 1A + 2A + 3 + 4 + docs.
- This session: Phase 2 audit site 1 (resolver), Phase 2 audit
  site 2 (typecheck_type cpp_name path), Phase 4b (end-of-body
  resolution sweep that succeeds on 241 components per
  dog-food run), graceful-error for unnamed-struct member
  access, this review document.

cbmc-cpp regression suite is green at 675/0/83.  Dog-food is
14 OK_CLEAN / 5 OK_NOISY / 98 FAIL / 0 CRASH (improved from
the pre-lazy-elaboration baseline of 10/4/103/0; the +5
absolute change is structural, with zero regressions across
117 files).

The architectural items in this review are the next set of
levers, in the order recommended above.


## 2026-05-24 Pack-substitution fix + reconfirmation of trait root cause

### Two fixes landed this session

1. **`template_map`: variadic pack substitution for nested template
   types** (commit `44ab8dee05`).  The pack-substitution code in
   `cpp_instantiate_template.cpp` (lines 2218 / 3754) and
   `cpp_typecheck_method_bodies.cpp` (line 96) used naive
   `tag.rfind("::")` to strip the namespace from a struct-tag
   identifier when substituting a pack parameter name.  For a nested
   template like
   `std::__cxx11::tag-basic_string<char,std::tag-allocator<char>>`,
   the `rfind` lands inside the inner `<...>` template arguments and
   yields the corrupted name `tag-allocator<char>>` (with a stray `>`
   inherited from the outer template's closing bracket).  This name
   was then injected into the `Params` parameter type of any function
   template instantiated with `std::string` arguments — most visibly
   `invariant_violated_structured<invariant_failedt, std::string>` —
   producing the cascade error
   `symbol 'tag-allocator<char>>' is unknown`.

   Fix: substitute with the **full** struct-tag identifier (including
   namespace prefix and `tag-` markers).  `resolve_scope` already
   knows how to find this directly via `id_map`/`symbol_table`.  Also
   added a fallback in `cpp_typecheck_resolvet::resolve` for
   single-name cpp_names whose identifier already contains `tag-`.

   Impact: eliminated all 60 `invariant_violated_structured`-style
   dog-food failures.  The 80-file FAIL count itself didn't change
   (the same files have other downstream failures, see below) but
   3 files moved from OK_NOISY to OK_CLEAN.

2. **`expr2c`: `id_shorthand` should prefer base_name and use
   depth-aware `::`** (commit `2bb468a367`).  Cosmetic but important
   for diagnostics.  The display path used `rfind("::")` to extract a
   shorthand from a symbol's full identifier; for any symbol with a
   `std::string` parameter, the mangled name contains
   `ref_struct_tag(identifier=std::tag-basic_string<...>)`, and the
   naive `rfind` produces fragments like
   `tag-allocator<char>>,#constant=1_1))` instead of the actual
   function name.  Two fixes:
   - When the symbol is in the symbol table and has a non-empty
     `base_name`, use it directly (the previous suffix check failed
     for function symbols whose mangled identifier ends with `)`).
   - For the `rfind` fallback, walk the string tracking
     angle-bracket depth so only depth-zero `::` separators are
     considered.

   With this fix, dog-food error candidates that previously displayed
   as `tag-allocator<char>>,#constant=1_1))(...)` now correctly show
   as `invariant_violated_string(...)`, exposing the real overload
   resolution failure (`char[N]` → `const std::string&` conversion
   not happening).

### Confirmed: invariant_violated_string failures = missing
### `basic_string(const char*, const Allocator&)` constructor

With clear error messages from fix #2, the surviving 22
`invariant_violated_string` dog-food failures point at one specific
diagnostic:

```
src/util/irep.h:177:1: error: found no match for symbol
  'invariant_violated_string', candidates are:
  symbol void invariant_violated_string(
    const struct basic_string &, const struct basic_string &,
    const signed int, const struct basic_string &,
    const struct basic_string &) (file src/util/invariant.h line 275)

argument types:
  char [16l]
  char [14l]
  signed int
  char [21l]
  char [13l]
```

The `PRECONDITION` macro passes 4 string literals + 1 line number.
Implicit conversion `char[N]` → `const std::string&` requires routing
through `std::basic_string`'s `(const char*, const Allocator&)`
converting constructor.  Direct comparison of basic_string component
lists between a working TU (`<string>` only) and a failing TU
(`<string>` plus CBMC's headers) confirms:

| Constructor | Simple TU | Dog-food TU |
|---|---|---|
| `(this, const char*, allocator=default)` — 3 params | **PRESENT** | **MISSING** |
| `(this, const char*, size_t, allocator=default)` — 4 params | present | present |
| ... 8 other ctors ... | identical | identical |

The missing 3-param constructor is the only one whose libstdc++
declaration is wrapped in
`template<typename = _RequireAllocator<_Alloc>>`, exactly as
documented in the previous "Group 2" investigation.  When CBMC
elaborates `basic_string<char>` in a TU with many template
instantiations, the SFINAE wrapper's substitution
(`enable_if<__is_allocator<_Alloc>::value, _Alloc>::type`) fails to
evaluate, the constructor is dropped, and downstream `char[N]` →
`std::string` conversion has no path.

This empirically reconfirms the previous review's analysis: the same
trait-evaluation root cause underlies both:
- 37 `sharing_treet`-instantiation failures (swap deduction's
  `_Require<__not_, is_move_constructible, is_move_assignable>`).
- 22 `invariant_violated_string`-call failures (constructor
  conversion's `_RequireAllocator<_Alloc>`).

### Recommended next session: Path 2 from 2026-05-22 review

The previous attempt at trait emulation (full struct synthesis at
`instantiate_template` time) failed because synthesised structs were
incomplete (`value` only, missing `value_type`/`type`/operators).
The recommended path forward — **intercept at resolve time** — has
not yet been tried:

When `cpp_typecheck_resolvet::resolve` is invoked on a cpp_name with
the shape `KnownTrait<args>::value`:
- Compute the constant directly (without instantiating the trait).
- Return a `from_integer(value, bool_typet{})` expression.
- Skip the partial-specialisation matching that's failing.

Known traits with mechanical evaluation:
- `__is_allocator<std::allocator<...>>::value` → `true`
- `__is_allocator<X>::value` for non-allocator X → `false`
- `is_move_constructible<T>::value` → `__is_constructible(T, T&&)`
- `is_move_assignable<T>::value` → `__is_assignable(T&, T&&)`
- `__not_<X>::value` → `!X::value` (recurse)
- `__and_<X, Y, ...>::value` → `X::value && Y::value && ...`

This avoids the synth-as-replacement pitfall: we never produce a
struct symbol that competes with libstdc++'s integral_constant
hierarchy.  The interception happens purely at the constant-value
evaluation level.

Estimated effort: 2-3 days, focused.  Highest-leverage remaining
unblocker (66 of 80 dog-food failures = 82%).

## Status as of 2026-05-24

35 commits ahead of pushed `ef662777b0`.  cbmc-cpp regression suite
green at 675 / 0 / 83.  Dog-food: 15 OK_CLEAN / 22 OK_NOISY / 80 FAIL
/ 0 CRASH (up from session-start 12 / 25 / 80 / 0 — variadic
pack-substitution fix moved 3 files from OK_NOISY to OK_CLEAN by
eliminating the cascade caused by the pack-name corruption).


## 2026-05-24 (continued) Path 2 trait intercept attempt — refined diagnosis

### Approach attempted

Implemented Path 2 (resolve-time trait interception) by adding two
hooks:

1. `try_intercept_trait` at the entry to `cpp_typecheck_resolvet::resolve`,
   matching cpp_names with the shape `[std::]Trait<args>::value` and
   short-circuiting them to `from_integer(value, bool_typet{})`.
2. An alias-template intercept at the `apply_template_args`
   default-argument evaluation site (around line 5187 in
   `cpp_typecheck_resolve.cpp`), recognising
   `_RequireAllocator<X>` / `_RequireInputIter<X>` /
   `_RequireNotAllocator<X>` and synthesising the result type
   directly from the first template argument.

Both hooks were exercised correctly via tracing (`CBMC_TRAIT_TRACE`
and `CBMC_DEFAULT_TRACE` env vars) and matched the expected
patterns.  The hooks were correctly invoked — but did not fix the
original missing-constructor symptom.

### Diagnosis of why both hooks didn't help

**Hook 1 — `__is_allocator<X>::value` never appears in resolve():**
Tracing showed CBMC processes ~500 distinct trait cpp_names per
dog-food file (`is_const`, `is_convertible`,
`is_trivially_destructible`, `__and_`, `__or_`, …) but
**zero** `__is_allocator` cpp_names.  That trait is never resolved
through `cpp_typecheck_resolvet::resolve` in the failing TU.

This refutes the previous review's hypothesis that
`__is_allocator<_Alloc>::value` evaluation is the failure point.
Instead the SFINAE wraps fail much earlier, before the inner
`__is_allocator<...>::value` cpp_name is even visited.

**Hook 2 — alias intercept fires but the ctor is still dropped:**
Direct empirical test with a minimal reproducer
(`#include <string>\n#include <bits/locale_classes.h>`) confirms
the const_char ctor count for `basic_string<char>` drops from 2
to 1 even when the alias intercept fires successfully on every
`_RequireAllocator<_Alloc>` default-arg evaluation.

Cause: `apply_template_args` is called during
**conversion-time overload resolution**, not during
**class-elaboration** member instantiation.  The 3-arg
`basic_string(const char*, const Allocator& = Allocator())`
constructor is dropped while `basic_string<char>`'s class members
are being added to its components list — and that elaboration
path bypasses `apply_template_args` entirely.

### Reproducer pinned to a specific include

A 3-line reproducer triggers the bug:

```cpp
#include <string>
#include <bits/locale_classes.h>
void f() { std::string s = "hello"; }
```

With this TU, `basic_string<char>`'s components list contains the
4-arg `(const char*, size_type, allocator)` ctor but is missing
the 3-arg `(const char*, allocator)` ctor.  Removing
`<bits/locale_classes.h>` (or replacing it with `<iosfwd>`)
restores the missing ctor.

This narrows the problem from "dog-food TU vs simple TU" to
"`<string>`-only TU vs `<string>` + `<bits/locale_classes.h>` TU"
— a much more tractable A/B for further investigation.

### Key trace observation

With debug instrumentation in `apply_template_args`
default-argument evaluation, the trace for the broken case
shows `_RequireAllocator<...>` defaults entering with
`first_arg.id == cpp_name::_Alloc` (still a template parameter
reference) — i.e., `template_map.apply` does **not** substitute
`_Alloc` to the concrete allocator type at this call site.  In
the simple case, the same code path is **not entered** for
`_RequireAllocator` at all — the constructor must be elaborated
through a different mechanism that doesn't reach here.

### Where the actual failure lives

The 3-arg ctor's silent dropping happens during
`typecheck_compound_body` member processing, specifically in
the path that "instantiates with defaults" template constructors
that have all-defaultable template parameters (e.g.,
`template<typename = X>`).  When `typecheck_type(X)` throws
during this elaboration step, the constructor symbol is not
added to the class's components list.

The throwing call path goes through `resolve_template_alias` for
`_RequireAllocator<_Alloc>`, which then attempts to
**instantiate** the alias body
`enable_if<__is_allocator<_Alloc>::value, _Alloc>::type`.  The
instantiation fails before `__is_allocator<_Alloc>::value` is
reached as a cpp_name.  Likely failure: `enable_if` or
`__is_allocator` partial-specialisation matching fails in the
post-`<bits/locale_classes.h>` elaboration state because some
intermediate template (e.g., `__is_allocator`'s primary
template's `__void_t<...>` argument) is in a different state in
the polluted scope.

### Refined recommendation for the next session

The right intercept point is **not** `resolve()` and **not**
`apply_template_args` default-arg evaluation.  It is during
`typecheck_compound_body`'s template-constructor processing,
when all-defaultable template parameters are evaluated to
"specialise" the template ctor into a regular components-list
ctor.  Specifically:

1. Find the code that calls `typecheck_type` on a class
   template's defaultable template parameter during
   `typecheck_compound_body`.
2. At that site, recognise libstdc++'s SFINAE-only alias
   templates by name (`_RequireAllocator`, `_RequireInputIter`,
   `_RequireNotAllocator`, possibly more) and synthesise the
   result without instantiating the alias.
3. Verify that the synthesised result causes the constructor
   to be added to the class's components.
4. Verify on the dog-food TU.

This is where Hook 2 should live.  The infrastructure code
landed in this session's working tree is reusable — only the
call site needs to be moved from `apply_template_args` to
`typecheck_compound_body`'s template-member elaboration.

This is still a 1-2 day focused project, but with the bug now
pinned to a 3-line reproducer and the intercept logic
prototyped, the remaining work is identifying the exact call
site in `typecheck_compound_body` and re-running the same
intercept there.

### Status

Reverted all in-progress changes (no commit).  Working tree
clean.  35 commits ahead of pushed `ef662777b0` (unchanged).
Documentation updated.


## 2026-05-25 brace-init in ctor calls — investigation deferred

### What's broken

31 dog-food files (the same 31 previously blocked by
`with_source_location`, now unblocked) hit the next error in
their chain at `src/util/type.h:38`:

```cpp
typet(irep_idt _id, typet _subtype)
  : irept(std::move(_id), {}, {std::move(_subtype)})
{}
```

CBMC reports:

```
found no match for symbol 'irept', candidates are:
  irept(struct irept *, const struct dstringt &, const struct
        forward_list_as_mapt &, const struct vector &)
  ...
argument types:
  struct dstringt
  <<type:>>
  <<type:>>
```

The `<<type:>>` strings come from `expr2c` printing a type with
empty `id()`.  Tracing the candidates and operands shows that
the brace-init args `{}` and `{std::move(_subtype)}` reach
overload resolution as

```
op[2].id=initializer_list type.id=  operands=0
op[3].id=initializer_list type.id=  operands=1
```

— `initializer_list` expressions whose `type.id()` is empty.
The candidate parameters are `pointer` types (CBMC's
representation of `const T &`) with class-tag base types.

`cpp_typecheck_fargst::match` only accepts brace-init operands
when the parameter type is exactly `tag-initializer_list<...>`.
For any other class-typed reference parameter, match returns
false and the candidate is rejected.

A 3-line reproducer:

```cpp
struct dstringt { dstringt() {} };
struct irept {
  using subt = std::vector<irept>;
  using named_subt = std::vector<irept>;
  irept() {}
  irept(const dstringt&) {}
  irept(const dstringt&, const named_subt&, const subt&) {}
  irept(const irept&) {}
};
struct typet : irept {
  typet() {}
  typet(dstringt _id, typet _subtype)
    : irept(std::move(_id), {}, {std::move(_subtype)}) {}
};
```

CBMC produces the same `found no match` cascade.

### Why a naïve fix doesn't work

Two attempts were made and reverted:

1. **Relax `match` to accept brace-init for class-typed
   parameters.**  Adding a fallback at distance 4 — viability
   only, dispatching the actual conversion to
   `implicit_typecast` later — made the reproducer report a
   secondary `invalid implicit conversion from '<<type:>>' to
   'const struct vector &'` (the actual conversion still has
   no path), but more critically broke
   `regression/cbmc-cpp/cpp11_future_header` — a clean
   `#include <future>` + empty main — with a stack overflow.
   GDB shows ~13 000 stack frames in
   `sharing_treet::remove_ref` destruction.

   The relaxation must be allowing some deeply nested ctor
   chain to be selected somewhere in `<future>`'s template
   machinery; the resulting expression tree is so deep that
   destructor recursion blows the stack.  The match
   relaxation is correct in shape but unsafe in practice
   without changing the recursive `sharing_treet::remove_ref`
   to an iterative form, or somehow guarding against
   pathological expression depth.

2. **Add `empty-brace-{} → reference-to-class` handler in
   `implicit_typecast`.**  Synthesises a default-constructed
   temporary and binds the reference.  This handler alone
   (without the match relaxation) was safe — it didn't break
   anything — but didn't help because `match` still rejects
   the candidate before `implicit_typecast` is reached.

### Options for the next attempt

* **Make `sharing_treet::remove_ref` iterative.**  This is the
  precondition for almost any future overload-resolution
  relaxation.  The destructor recursion depth is bounded by
  the depth of the irept tree, which can grow arbitrarily
  large in pathological CBMC-internal trees produced during
  C++ template machinery typecheck.

* **Type the brace-init-list lazily based on the candidate
  parameter type.**  Inside `match()` (or earlier, inside
  `cpp_typecheck_fargst::build`), recognise `initializer_list`
  operands and synthesise a typecheck of them against each
  candidate parameter type before measuring viability.  This
  matches list-initialization semantics (per [dcl.init.list])
  and would avoid the "untyped operand" symptom entirely.

* **Ship the `empty-brace-{}-to-reference` handler in
  `implicit_typecast`** as a stand-alone improvement.  It
  doesn't fix the dog-food failures by itself but is a
  correct, safe change that future work can build on.

The third option is small and safe; the first two are 2-3 day
projects.

### Status

Reverted all in-progress changes.  Working tree clean.
Documentation updated.  Dog-food unchanged at 19 / 18 / 80 / 0;
cbmc-cpp regression suite green at 678 / 0 / 83.


## 2026-05-26 Option 2 attempt — proper [over.match.list] viability and conversion

### Approach

Implemented [over.match.list]-conforming brace-init viability in
`cpp_typecheck_fargst::match` plus the corresponding conversion
in `cpp_typecheckt::implicit_typecast`.  Three viability paths,
matching [dcl.init.list]/3:

1. Empty `{}` — viable iff the destination class type has an
   accessible default constructor (or is an aggregate).  The
   conversion synthesises a `temporary_object` wrapped in
   `address_of` for reference targets.
2. Non-empty `{x_1, ..., x_n}` — viable iff the class has an
   accessible `initializer_list<U>` constructor.  The
   conversion recurses through `implicit_typecast` to first
   build an `initializer_list<U>` value (via the existing
   brace-to-initializer_list handler), then calls
   `new_temporary` to construct the destination class.
3. Non-empty for an aggregate type with matching field count —
   already handled by the existing aggregate-init block; the
   match viability check defers to it.

### What worked

* Empty `{}` viability and conversion: the
  `cpp11_future_header` regression continues to pass (after
  filtering out `std::chrono::` / `std::tag-ratio<` /
  `std::__detail::` whose default-construction triggers
  pathological constexpr ratio reduction in CBMC's elaboration).
* All 678 cbmc-cpp regression tests stay green.

### What blocked Option 2

The non-empty-brace path runs the recursive `implicit_typecast`
to build an `initializer_list<U>` value, then calls
`new_temporary(class_type, initializer_list_value)` to invoke
the destination class's `initializer_list<U>` ctor.  Two issues:

1. The intermediate value is a `struct_exprt` (id `ID_struct`)
   whose downstream typecheck cannot accept it (hits the
   `unexpected expression: struct` path in
   `c_typecheck_baset::typecheck_expr_main`).

2. `new_temporary`'s constructor resolution does not reliably
   pick the `initializer_list<U>` ctor when the argument is a
   `struct_exprt` of `initializer_list<U>` — `cpp_constructor`
   expects argument expressions whose categories (rvalue/lvalue,
   temporary_object marker) match what reference-binding
   produces in normal call flow, not what
   brace-to-initializer_list synthesises.

Both issues are fixable in principle but require either:

* Wrapping the synthesised initializer_list in a `temporary_object`
  marker so reference binding accepts it, **and**
* Auditing the brace-to-initializer_list handler to ensure the
  array-symbol address-of is produced as an lvalue throughout
  (the array symbol uses `is_lvalue=true` in the symbol_table
  but the wrapping `symbol_exprt` doesn't carry the flag, which
  surfaced the `not an lvalue` error during the recursion).

### Empirical state with full Option 2 implementation

The full implementation (with both empty and non-empty paths)
**advanced** all 31 dog-food files past the
`found no match for symbol 'irept'` error, but they all hit the
same downstream `unexpected expression: struct` error because of
the issue described above.  Net dog-food file-count change: 0.
The empty-only partial implementation also doesn't move the
count, because every dog-food irept ctor call pairs an empty
`{}` with a non-empty `{x}` argument and the candidate is
rejected for the non-empty arg.

### Forward path

A correct Option 2 implementation needs the brace-to-class
non-empty-brace conversion to produce a usable `temporary_object`
that subsequent typechecking accepts.  The simplest sketch:

```cpp
// In implicit_typecast, after recursing to build init_list<U>:
// wrap the struct_exprt in a temporary_object so it presents
// as an rvalue of class type.
side_effect_exprt il_temp{
  ID_temporary_object, {std::move(init_list_value)},
  init_list_param_type, src_loc};
il_temp.set(ID_mode, ID_cpp);
il_temp.set(ID_C_lvalue, true);
new_temporary(src_loc, base_type, il_temp, temp);
```

plus making the array-symbol-expr inside the brace-to-init_list
handler properly carry `ID_C_lvalue` end-to-end so the recursive
case is robust.

This is a 1-2 day focused project.  The key risk is that the
recursion through `implicit_typecast` and `new_temporary` opens
new paths in `<chrono>`/`<future>`/`<thread>` template
machinery, which has historically tripped pathological
elaboration depth — so any final implementation needs both the
allowlist filter (already present in the empty-`{}` path here)
**and** integration testing on a broad set of standard headers,
not just `cpp11_future_header`.

### Status

Reverted all source changes.  Working tree clean.  Documentation
updated.  Dog-food unchanged at 19/18/80/0; cbmc-cpp regression
suite green at 678/0/83.


## 2026-05-26 std::unordered_map / std::vector member-access elaboration

### Symptom

18 dog-food files fail with

    src/util/std_types.h:757:1: error: symbol 'reserve' is unknown
        parameter_indices.reserve(params.size());

at the call site

    parameter_indicest pi;     // typedef of unordered_map<irep_idt, std::size_t>
    pi.reserve(params.size());

A standalone reproducer (`/tmp/reserve_repro11.cpp`):

```cpp
#include <unordered_map>
#include <string>

struct code_typet
{
  typedef std::unordered_map<std::string, std::size_t> parameter_indicest;

  void f() const
  {
    parameter_indicest pi;
    pi.reserve(16);   // "symbol 'reserve' is unknown"
  }
};

int main() { code_typet ct; ct.f(); return 0; }
```

triggers it.  The same construct without the typedef (using
`std::unordered_map<...>` directly in the method body) works.

### Root cause

`cpp_typecheckt::typecheck_compound_body`'s body loop iterates
the 126 sub-elements of libstdc++'s `std::unordered_map<...>`
declaration body.  Iteration 5 (somewhere in the public-section
declarations — could not narrow further without a deep trace
across the chain of helper calls) throws `int 0`.  The throw
escapes the body loop, leaving only the private `_Hashtable`
typedef and `_M_h` data member registered as components.
`reserve` and all other public methods of `unordered_map` never
register.

The first call site (e.g. `pi.reserve(16)` after the typedef
has been processed) calls `elaborate_class_template`, which
sees the symbol is "complete" (`is_incomplete=false`,
`components > 0`) and skips re-elaboration.  Member lookup for
`reserve` then fails because the only components are
`_Hashtable` and `_M_h`.

A secondary issue: in `typecheck_compound_type`'s "previously
incomplete becomes complete" path at line ~218,
`writeable_symbol.type.swap(type)` replaces the symbol's type
with the parser's complete type and loses the
`ID_template_class_instance` flag set by
`cpp_instantiate_template.cpp:372`.  Two adjacent flags
(`ID_C_template`, `ID_C_template_arguments`) are explicitly
preserved across the swap; `ID_template_class_instance` is not.
After the swap, downstream consumers see
`template_class_instance=false` even though the symbol *is* a
template instance.

### Two-part fix attempted

1. Preserve `ID_template_class_instance` across the
   `writeable_symbol.type.swap(type)` (one-liner addition next
   to the existing two preserve calls).
2. Wrap each body-loop iteration in `try { ... } catch(int) { ... }`
   gated on
   `!instantiation_stack.empty() && template_class_instance`,
   matching the recovery pattern already in use for
   `convert_template_declaration` and base-class elaboration.

### Why it didn't land

The recovery makes the `reserve_repro11` case compile —
`unordered_map`'s components fully register and `reserve`
resolves.  But it also exposes a cascade of downstream bugs
that invariant-violate or crash in other tests:

* `cpp20_vector_basic` regression: hits "symbol '__it' is
  unknown" inside concept evaluation at C++20 vector iterator
  elaboration once the body loop continues past the iter-5
  throw.
* `cpp11_future_header` and the `reserve_repro11` reproducer
  itself: subsequent template elaboration walks a
  partially-elaborated `<chrono>` / `<future>` class structure
  and trips
  `Invariant ... can_cast_type<struct_tag_typet>(type)` in
  `to_struct_tag_type` at `src/util/std_types.h:519`.

The throw isolation is correct in principle but the rest of the
typecheck / elaboration pipeline assumes an "all-or-nothing"
result from class instantiation.  Once the body loop is allowed
to recover, code paths that walk struct components, look up
members, or inspect iterator types encounter partially-
elaborated structures they were never designed to tolerate.

A safe landing of this fix needs either:

* Identifying the specific declaration in iteration 5 of
  `unordered_map`'s body that throws `int 0`, fixing it in-place
  (so the body loop completes cleanly without recovery), and
  *then* the swap-preservation alone (no try/catch) suffices.
* Or auditing every downstream consumer of class-template
  components / member lookup to handle partial elaboration
  gracefully — this is a much larger architectural project,
  comparable in scope to the original "throw escapes body loop
  in template instantiation" recovery added for
  `typecheck_compound_bases`.

### Status

Reverted; documented here.  Dog-food remains at 20 / 17 / 80 / 0.
The 18 `'reserve' is unknown` failures stay open.

The two proper next-step paths above are tracked but neither
fits this session's scope safely.


## 2026-05-26 (continued) Path-1 vs path-2 attempts and the `baset::type()` precondition trap

### Summary

Two follow-up sessions on `'reserve' is unknown` explored both:
- **Path 1**: fix the iter-5 throw at its source.
- **Path 2**: audit downstream consumers to tolerate partial elaboration.

Path 1 traced cleanly into the cascade:

```
unordered_map iter 5: typedef typename _Hashtable::key_type key_type;
  → typecheck_type(`_Hashtable::key_type`) throws
  → resolve(`__hashtable_alloc::__node_ptr`) throws inside `_Hashtable<...>` scope
  → resolve(`__base_type::value_type`) throws inside `_Insert<...>` scope
  → resolve(`_Hashtable_alloc<...>`) throws inside `_Insert_base<...>` scope
  → resolve(`__node_alloc_traits::rebind_traits<...>`) throws inside
    `_Hashtable_alloc<...>` scope
  → resolve(`__get_value_type<X>::type`) throws inside
    `_Hashtable_alloc<...>` scope
```

The chain bottoms out at `__get_value_type<_Hash_node<_Val,
_Cache_hash_code>>::type`, a class-template **specialization** match
inside `std::__detail::_Hashtable_alloc<...>` that CBMC's template
machinery does not resolve while the enclosing class is mid-body.

Path-1 fix would need to teach CBMC to either eagerly elaborate
`__get_value_type<...>` specializations during body processing of the
enclosing template, or to defer the typedef and resolve it on first
use.  Both are larger-scope template-machinery changes than fits this
session.

### Path 2 findings

Three attempts at making downstream consumers tolerate partial
elaboration:

1. **Body-loop recovery, broad (catch all `int`)**.  Lets every
   throwing body iteration recover, gated on
   `!instantiation_stack.empty() && template_class_instance`.
   Requires preserving `ID_template_class_instance` across the
   incomplete-to-complete `type.swap()`.  Crashes
   `cpp20_vector_basic` and `cpp11_future_header` on `to_struct_tag_type`
   precondition violations once the recovery path drives downstream
   code into partially-elaborated structures.

2. **Body-loop recovery, typedef-only**.  Same shape as (1) but
   restricted to `decl.is_typedef() && !decl.is_template()`.  Vector
   passes (with hardening from this commit's safety guards), but
   `cpp20_span_basic` regresses to a `'__it' is unknown` CONVERSION
   ERROR.  `__it` is a parameter inside C++20
   `requires(_Iter __it) { ... }` clauses; the recovery lets span's
   body proceed far enough to start instantiating
   `std::__detail::__cpp17_iterator<...>`'s requires-clause body,
   which CBMC's parser/elaborator does not fully model, hence the
   "is unknown" error.

3. **Lazy typedef registration during instantiation**.  When a
   typedef whose aliased type is a qualified `cpp_name` throws,
   restore the unresolved cpp_name and route through the existing
   `kept_unresolved_cpp_name` lazy-typedef registration path.
   Sibling members no longer see "unknown typedef" errors on use,
   but methods that resolve the lazy typedef in their parameter or
   return type still throw.  Net effect on dog-food: 8 files move
   `clean → noisy` (lazy uses surface as warnings) without reducing
   the 80 fails.  Reverted.

### `baset::type()` precondition trap

A subtle issue that delayed the get_base fix:
`struct_typet::baset::type()` returns a `struct_tag_typet&` and is
implemented as `return to_struct_tag_type(exprt::type());`.  The
`to_struct_tag_type` precondition lets the compiler conclude (under
optimisation) that `b.type().id() == ID_struct_tag` always, which
silently elides any `can_cast_type<struct_tag_typet>(b.type())` guard
written *in front of* a `to_struct_tag_type` call inside the loop —
the guard simply doesn't appear in the emitted code.  The fix has to
bypass `baset::type()` and read the type field directly via
`irept::find(ID_type)` to keep the guard alive.  This is what the
`ed2c374384` commit's `get_base` rewrite does.

### Two safety guards landed (commit `ed2c374384`)

* `struct_typet::get_base(id)` reads its base's type through
  `irept::find` so it can skip non-`struct_tag` entries instead of
  triggering `to_struct_tag_type`'s PRECONDITION.
* `cpp_typecheckt::elaborate_class_template(type)` early-returns on
  empty tag identifier instead of triggering
  `lookup(to_tag_type(type))`'s namespace-lookup invariant.

Both are reached from sites that already have try/catch or SFINAE
recovery — the previous abort defeated that recovery, turning a
recoverable diagnostic into a hard crash.

Full cbmc-cpp regressions (678/0/83) pass.  Dog-food unchanged at
20 / 17 / 80 / 0.

### Open status

The 18 `'reserve' is unknown` failures stay open.  A safe landing
needs the path-1 deep fix (teach the template machinery to handle
metafunction specialization match during enclosing-class body
elaboration), or a path-3 mechanism not yet identified that would
register `unordered_map`'s public methods (`reserve`, `insert`,
`find`, ...) without requiring the typedefs in iters 5–11 of its body
to resolve.


## 2026-05-27 Template specialization matching with variadic packs (deep dive)

Investigation of the deeper template-machinery work needed to unblock
the `__get_value_type<_Hash_node<...>>::type` cascade that's behind
the dog-food `'reserve' is unknown` failures (and most of the other
stdlib-template categories).

### Root-cause chain

The failure is driven by `__alloc_rebind<_Alloc, T>` not resolving
correctly.  In libstdc++:

```cpp
template <typename _Tp, typename _Up>
  struct __replace_first_arg
  { };

template <template <typename, typename...> class _SomeTemplate,
          typename _Up, typename _Tp, typename... _Types>
  struct __replace_first_arg<_SomeTemplate<_Tp, _Types...>, _Up>
  { using type = _SomeTemplate<_Up, _Types...>; };
```

For `__replace_first_arg<allocator<pair<...>>, _Hash_node<pair<...>>>`,
the partial specialization should match (with
`_SomeTemplate = allocator`, `_Tp = pair<...>`, `_Types = ()`,
`_Up = _Hash_node<...>`) and yield
`allocator<_Hash_node<pair<...>>>`.

CBMC silently falls through to the primary template (which has no
`type` member) and produces the *unrebound* `allocator<pair<...>>`,
which then mismatches the inner `__get_value_type<_Hash_node<...>>`
specialization.  That's how the dog-food failures bubble up to the
visible `'reserve' is unknown` / `'iterator' is unknown` errors.

### Three layered bugs in CBMC

Built a standalone reproducer (`/tmp/specmatch_rebind4.cpp`) that
mirrors the libstdc++ pattern.  Tracing through
`disambiguate_template_classes`,
`cpp_typecheck_resolvet::guess_template_args` and
`template_mapt::apply` revealed three distinct bugs that all need
fixing for the spec match to succeed:

1. **Pack-parameter deduction loop**.  The deduction loop runs
   `min(targs.size(), inst_arguments.size())` iterations.  When the
   partial spec's args list contains a pack reference (`_Types...`)
   represented as an `ambiguous(type=cpp_name(ellipsis=true))` and
   the desired-type's args are shorter, the pack parameter never
   gets a binding.  `has_unassigned()` rejects the spec.

2. **`matcht::operator<` cost is wrong**.  `cost = _s_args.arguments().size()`.
   For a partial spec with extra template parameters introduced by
   a pack, the spec's cost exceeds the primary's cost (its argument
   list is the full template-parameter list, not the partial-spec
   pattern), so the primary wins on tie-break even when the spec
   would otherwise have been the more specialised match.  Adding a
   bare `is_primary` flag and letting any spec beat the primary on
   ties resolves it.

3. **TT-param substitution drops the template name**.  When a
   template-template parameter `_SomeTemplate` is bound to a
   struct_tag (e.g. `allocator<A>`, the whole instance — that's
   how CBMC currently records TT-param bindings), and a spec body
   refers to `_SomeTemplate<_Up, _Types...>`,
   `template_mapt::apply` falls into
   `if(has_targs || sub.size() == 1) { ... type = entry.second;
   return; }` and replaces the whole `_SomeTemplate<...>`
   expression with the bound `allocator<A>` instead of substituting
   only the *name* and re-applying the args.  Net result:
   `_SomeTemplate<_Up>` becomes `allocator<A>` instead of
   `allocator<_Up>` (which after `_Up = B` substitution would be
   `allocator<B>`).

   A fix that extracts the bound template's `base_name` from the
   `tag-<base><args>` form of the struct_tag identifier (no
   symbol-table lookup needed since `template_mapt` is
   stand-alone) and rewrites only the front-name of the cpp_name
   correctly produces `allocator<_Up>`, leaving the existing
   args-substitution loop to substitute `_Up = B` and expand the
   empty `_Types...` pack.

### Where the implementation hits a wall

A four-file patch wiring up all three fixes (deduction-loop pack
handling, `is_primary` tie-break, TT-param front-name rewrite, and
`build_template_args` omitting empty pack args + `build` always
recording empty `pack_args_map[id]`) makes the deduction find the
spec and produces the correct `tag-allocator<tag-B>` for `R`.

But two more issues surface:

* **Nested-elaboration scope leak**.  Once `R = allocator<B>` is
  produced, accessing `R::value_type` walks
  `tag-allocator<tag-B>`'s body — which is left as an *incomplete*
  shell because no caller forces its elaboration.  The fallback
  path resolves `value_type = _Tp` against the *outer* (spec's)
  template_map, where `_Tp = A`, and produces
  `R::value_type = A`.  The reproducer confirms `y : struct tag-A`
  in the GOTO output even though `R = allocator<tag-B>`.  Fixing
  this requires triggering elaboration of nested instances on
  member-access *and* ensuring the inner instance's template_map
  isolates its `_Tp` from the outer scope.

* **`build_template_args` regression**.  Omitting empty pack args
  from the typechecked args list breaks
  `cpp11_variadic_pack_short_name_collision`, which depends on
  short-name-keyed `pack_size_map` entries persisting across the
  instantiation stack so that nested templates with same-named
  packs disambiguate correctly.  The fix would need to keep the
  shared-name semantics intact while still avoiding `has_unassigned`
  rejection of the spec.

### Status

Reverted; documented here.  The investigation is captured for the
next iteration:

* The deduction-loop pack-handling fix is the highest-value standalone
  change and is independent of the other two.  It's also the one that
  most directly maps to the `'reserve'` cascade root cause.
* The TT-param fix in `template_mapt::apply` is the most surgically
  contained but depends on (1) for the deduction to succeed in the
  first place.
* The `matcht::operator<` cost ordering is a pre-existing bug that
  predates the variadic-pack issue — any partial spec that introduces
  *any* extra template parameters (not just packs) hits it.

A safe landing needs all three fixes, the nested-elaboration scoping
fix, and a path through the `pack_size_map`-shared-name semantics
that doesn't regress `cpp11_variadic_pack_short_name_collision`.
That's a multi-day project and shouldn't be tackled as a single
session's commit.

Dog-food unchanged at 20 / 17 / 80 / 0.


## 2026-05-27 (continued) Three-fix landing for the spec-matching cascade

After the initial deep dive identified the three layered bugs in
template-specialization matching with variadic packs, this section
records the three fixes that landed (with their diagnostic refinements)
and the new stopping point.

### What landed

| commit | fix |
|---|---|
| `ba9b288a45` | TT-param-to-instance substitution preserving args (`template_mapt::apply`) |
| `752415ddfe` | Empty-pack sentinel handling in `template_mapt::build`/`apply` |
| `3bed1dffee` | Same-named-param shadowing in `template_mapt::build` (nested elaboration scope leak) |
| `fe24f929d5` | Regression tests `cpp17_replace_first_arg` and `cpp17_replace_first_arg_sizeof` |

### How the three fixes compose

For `__replace_first_arg<allocator<A>, B>::type`:

1. `elaborate_class_template`'s spec-matching path
   (`cpp_instantiate_template.cpp:1115+`) deduces the spec correctly
   (this was already the case — the post-loop empty-pack workaround
   at line 1213-1224 places an `empty_typet` sentinel for the
   zero-element pack so `has_unassigned()` doesn't reject the spec).
2. `instantiate_template` builds the template_map for the spec.
   `752415ddfe` makes `build` recognise the `empty_typet` sentinel and
   record a zero-size pack with no `pack_args_map` entry (instead of
   `pack_args_map[_Types] = [empty_typet]` with size 1).
3. The spec body's `using type = _SomeTemplate<_Up, _Types...>` is
   substituted by `template_mapt::apply`.  `ba9b288a45` makes
   `apply` rewrite only the front-name of the cpp_name when the
   TT-parameter is bound to a struct_tag (extracting the bound
   template's base name from the `tag-<base><args>` form), instead
   of replacing the whole expression with the bound instance.  The
   args-substitution loop then substitutes `_Up = B` and expands the
   empty pack via `pack_size_map[_Types] = 0` (the `apply` companion
   from `752415ddfe`).
4. `R = allocator<B>` is created.  Accessing `R::value_type` triggers
   nested elaboration of `tag-allocator<tag-B>`.  Without the
   `3bed1dffee` shadow fix, the outer spec's `_Tp -> A` binding
   (still in `type_map` because `cpp_saved_template_mapt` saves by
   COPY rather than clearing) leaks into the suffix-match for
   allocator's `_Tp` and `R::value_type` resolves to `A`.  With the
   shadow fix, allocator's own `_Tp -> B` removes the outer's
   same-suffix entry for the duration of the inner instantiation,
   and `R::value_type = B`.

### Test outcomes

* Standalone `/tmp/specmatch_rebind4.cpp` (b_field positive test):
  `R = allocator<B>`, `y = B`, `y.b_field = 42` succeeds.
* Standalone `/tmp/specmatch_rebind5.cpp` (a_field negative test):
  fails to typecheck `y.a_field = 42` because `R::value_type = B`
  (which has no `a_field`).
* Standalone `/tmp/scope_leak.cpp`/`scope_leak2.cpp` (no-pack
  variants of the same shadowing test): produce the right inner
  `_Tp` binding.
* `cpp11_require_swap` regression: the partial-spec test that was
  documenting the prior bug now actually verifies — `std::swap`
  through libstdc++'s `_Require<__not_<...>, is_move_constructible,
  is_move_assignable>` chain resolves successfully.
* New regression tests `cpp17_replace_first_arg{,_sizeof}` cover the
  fixed pattern.

### Bugs from the deep-dive section that did NOT need fixing

* **Bug #1 (pack-parameter deduction in `disambiguate_template_classes`)**:
  the `elaborate_class_template`-based spec-matching path
  (`cpp_instantiate_template.cpp:1115+`) is the one that actually
  fires in our case.  It already had a post-loop workaround that
  places `empty_typet` for unassigned pack params (line 1213-1224),
  so the spec is accepted.  `disambiguate_template_classes`'s deduction
  loop is reachable from other code paths but was not the blocker for
  the `__alloc_rebind` cascade.  No fix landed here; if it becomes the
  blocker for some other case, the same `empty_typet`-sentinel approach
  used in `elaborate_class_template` could be ported.

* **Bug #2 (`matcht::operator<` cost ordering)**: the same
  `elaborate_class_template` spec-matching path uses its own
  best-match selection (line 1632-1636: "first non-primary spec beats
  primary") rather than `matcht::operator<`.  The `matcht`-based
  scoring in `disambiguate_template_classes` may still be wrong for
  some cases, but it's not on the path that handles the dog-food
  cascade and didn't manifest in any current reproducer.

### Where the cascade now stops

`/tmp/reserve_repro11.cpp` (the headline reproducer for the
`'reserve' is unknown` cascade) still fails.  The new failure mode
is:

```
instantiating 'std::__alloc_rebind' with <struct allocator, struct _Hash_node>
instantiating 'std::__allocator_traits_base::__rebind' with <struct allocator, struct _Hash_node, void>
template scope 'rebind' is ambiguous
  std::__new_allocator<char>::template.rebind<Type0>
  std::allocator<char>::template.rebind<Type0>
  __gnu_cxx::__alloc_traits<std::tag-allocator<char>,char>::template.rebind<Type0>
  std::__new_allocator<char16_t>::template.rebind<Type0>
  std::allocator<char16_t>::template.rebind<Type0>
  ...
```

The `__alloc_rebind` chain progresses past `__replace_first_arg`
correctly (the rebind that previously aliased to the original
allocator now produces the rebound allocator), but resolution of
`rebind::other` then hits an ambiguous-scope error: every
already-instantiated `allocator<X>` has a member template `rebind`
in its scope, and the qualified lookup `_Alloc::rebind<U>::other`
finds all of them rather than just `_Alloc`'s own `rebind`.

This is a SEPARATE bug — qualified-name lookup through a struct_tag
should restrict to that one tag's members, not search across the
template_scopes of every same-base-name instance.  It does not
appear to be a regression introduced by the three fixes (the prior
state never reached this point because `__replace_first_arg`
silently aliased and the chain failed earlier).

### Status

cbmc-cpp regressions: 678/0/83 (one previously-failing test now
passes correctly); dog-food: 20/17/80/0 (the dominant Category-A
irept-body issue is unrelated and unaffected).

The three fixes plus the regression tests are independent landings
that don't depend on solving the `rebind`-ambiguity follow-up.  They
unblock the partial-specialization layer of the cascade and provide
a clean foundation for the next iteration to tackle the
qualified-lookup ambiguity.


## 2026-05-27 (continued) Qualified-name lookup for TT-param-bound qualifiers

The previous landing pushed the cascade past the partial-
specialization layer; the new stopping point in
`/tmp/reserve_repro11.cpp` was an "ambiguous template scope
'rebind'" error in libstdc++'s
`__allocator_traits_base::__rebind` partial-spec evaluation.

### What was happening

For `__rebind<allocator<pair<...>>, _Hash_node<...>, void>`, the
spec's third template arg is

```cpp
__void_t<typename _Tp::template rebind<_Up>::other>
```

Substituting `_Tp = allocator<pair<...>>`, this should look up
`rebind` in the *specific* allocator instance's scope.  CBMC was
instead reporting fifteen-plus candidates from across every
`allocator<X>` and `__alloc_traits<X>` instantiation in the
program.

Two interacting bugs combined to produce that:

1. **`template_mapt::apply`'s TT-param-with-args path was
   over-applied.**  The 2026-05-27 fix `ba9b288a45` (TT-param
   front-name rewrite) was correct for the original test case
   `_SomeTemplate<_Up, _Types...>` (no `::` in the cpp_name) but
   ran for any cpp_name with `has_targs=true`.  For a qualified
   form like `_Tp::rebind<_Up>::other`, the rewrite replaced only
   the front name with the bound template's bare base name —
   e.g. `_Tp` → `allocator` — and dropped the bound instance's
   own template arguments.  Net effect: the qualified lookup
   moved through to `std::tag-allocator` (the base template
   scope) instead of `std::tag-allocator<std::tag-pair<...>>`.

2. **`disambiguate_template_classes` fell back to a root-scope-
   recursive search for empty input id_sets.**  When the
   qualified-lookup arrived at the base template scope (per bug
   1) and found nothing, the fallback collected every same-base-
   name template across the program.  For `rebind` this is every
   member template of every `allocator<X>` instance.

### The fix (commit `e54bcdd520`)

* `template_mapt::apply` now distinguishes
  `_Tp<args>` (no `::` in the cpp_name → existing front-name
  rewrite) from `_Tp::name<args>::...` (`::` present → replace
  the front name with the bound struct_tag's full identifier so
  the qualified lookup happens in the right scope).
* `disambiguate_template_classes` accepts a `qualified` parameter
  (default false).  When true, both the root-scope-recursive
  fallback and the symbol-table-walk fallback are skipped — per
  [basic.lookup.qual] the lookup must be restricted to the
  qualified target's scope and base classes.
* The two call sites pass `qualified` accordingly:
  - `resolve_scope` (mid-cpp_name component) passes
    `qualified=!recursive` so unqualified-first-component
    fallbacks (e.g. `__int_traits<_Tp>::__digits` after `using`)
    keep their root-recursive behaviour.
  - `resolve` (final cpp_name component) passes through the
    existing `cpp_name.is_qualified()` flag.

A new regression test
`regression/cbmc-cpp/cpp17_alloc_traits_rebind` exercises the
pattern with multiple `allocator<X>` instantiations to protect
against re-introducing the ambiguity.

### New stopping point

`/tmp/reserve_repro11.cpp` now fails at:

```
file /usr/include/c++/13/type_traits line 2685:
  expected template name for template template parameter
```

This is in libstdc++'s `__detected_or_t`:

```cpp
template<typename _Default, template<typename...> class _Op,
         typename... _Args>
  using __detected_or_t
    = typename __detected_or<_Default, _Op, _Args...>::type;
```

The error suggests that the `template<typename...> class _Op`
template-template-parameter binding fails when `_Op` is
substituted with whatever the call site passes — likely a
template alias rather than a class template.  This is a separate
qualified-name / TT-param issue and is the next iteration's
target.

### Status

Five-commit landing (this session):

| commit | summary |
|---|---|
| `ba9b288a45` | TT-param-to-instance substitution preserving args (apply) |
| `752415ddfe` | Empty-pack sentinel handling in build/apply |
| `3bed1dffee` | Shadow same-named template params in build (nested elaboration) |
| `fe24f929d5` | cpp17_replace_first_arg{,_sizeof} regression tests |
| `e54bcdd520` | Qualified-name lookup for TT-param-bound qualifiers |

cbmc-cpp regressions: 679/0/83 (one previously-failing test
now properly verifies; two new regression tests added).  Dog-food
unchanged at 20/17/80/0 (dominated by the unrelated Category-A
irept-body issue).


## 2026-05-27 (continued) Three more cascade layers: TT-param alias forward, inherited conversion operators, constexpr eval safety

The previous landing pushed the cascade past the qualified-name
lookup ambiguity.  This session's three follow-on fixes push
through the next three layers; the cascade now stops at a
deeper-nested template-class method-body issue.

### What landed

| commit | summary |
|---|---|
| `e54bcdd520` | (previous session, recapped) Qualified-name lookup for TT-param-bound qualifiers |
| `3bae7b3527` | Forward already-resolved TT-param-bound TT-param argument |
| `a5bfd7c4da` | Include inherited cast operators in user-defined-conversion search |
| `2f3e2b37ca` | Reject un-resolved cpp_name in constexpr function-call eval result |

### The three bugs

#### Bug A: TT-param-alias-forward (3bae7b3527)

`__detected_or_t<Default, Op, Args...>` (libstdc++'s
"detect-or-default") forwards its `_Op` template-template
parameter to inner `__detected_or<Default, _Op, Args...>`.  At
the inner instantiation, the `_Op` argument arrives as an
`ambiguous` / `type_exprt` whose type is already a
`template_parameter_symbol_type` (the resolved binding from the
outer scope).

`typecheck_template_args`'s TT-param dispatch only handled
`cpp_name`-typed arguments.  When the argument was
already-resolved, the lookup branch was skipped and the function
fell through to "expected template name for template template
parameter".

Fix: detect the already-resolved TPST case and forward it
directly into `template_map`, normalising the args[i] entry from
`ambiguous` to `type_exprt` so the downstream `template_suffix`
invariant `expr.id() != ID_ambiguous` doesn't trip.

Test: `regression/cbmc-cpp/cpp17_tt_param_alias_forward`.

#### Bug B: inherited-conversion-operator (a5bfd7c4da)

`user_defined_conversion_sequence` skipped any component with
`from_base=true` when scanning for cast operators.  Per
[class.conv.fct]/1 + [class.member.lookup]/4 inherited
conversion operators are valid candidates in derived-class
lookup.

Concrete failure: libstdc++'s `__and_<Cs...>` inherits its
`operator bool()` from `integral_constant<bool, V>`, and code
such as `_Hashtable_enable_default_ctor<...>` has
`__and_<...>{}` as a non-type template argument.  The unconditional
skip silently filtered out the inherited operator and produced
"invalid implicit conversion from 'struct __and_' to 'bool'".

Fix: drop the `from_base` filter in the cast-operator scan
loop.  Standard rules (access, using-declarations) already
handle which inherited operators are visible.

Test: `regression/cbmc-cpp/cpp17_inherited_conversion_op`.

#### Bug C: constexpr-eval safety (2f3e2b37ca)

`typecheck_side_effect_function_call`'s constexpr-evaluation
block substitutes parameters in the function body and installs
the result in place of the call when a `has_calls` check
confirms the result is fully foldable.  The check rejected
remaining side effects and non-`code` symbol references but
missed unresolved `cpp_name` nodes.

When a class-scope `constexpr` member function references
same-class members (e.g. a static `value`) and the body hasn't
been type-checked in its own class scope yet, the body is still
in cpp_name form.  The substitute-and-install path then leaves
unresolved cpp_names in the caller's scope, where the
downstream typecheck of `value` fails with a "symbol 'value' is
unknown" diagnostic at a source location pointing back into the
function body — confusing because the actual lookup happens in
the caller's scope.

Fix: also reject `cpp_name` in the `has_calls` check.  This is
a defensive narrowing that prevents corruption of caller scopes
when an upstream body wasn't ready for constexpr folding.

### New stopping point

`/tmp/reserve_repro11.cpp` now stops at the chain that bug C
documents but doesn't fully fix:

```
instantiating 'std::_Hashtable_enable_default_ctor'
   with <struct equal_to, struct hash, struct allocator>
   at file /usr/include/c++/13/bits/hashtable.h line 233
symbol 'value' is unknown
file /tmp/reserve_repro11.cpp line 12 function f:
   symbol 'reserve' is unknown
CONVERSION ERROR
```

The static member `value` in `integral_constant<bool, V>` is
being looked up in `main`'s scope rather than in
`tag-integral_constant<bool, true>`'s scope.  This happens
because the template-class member function `get()` (or
`operator bool()`) hasn't been processed by
`typecheck_method_bodies` at the time the call result is needed
as a non-type template argument; the body's unqualified
`value` cpp_name reaches the caller without ever being resolved
in the function's own (class) scope.

The proper fix is to either:
1. Eagerly typecheck a constexpr method body before constexpr-
   evaluating it (so cpp_names get resolved in the function's
   class scope), or
2. Re-typecheck the body (or just the substituted result) in the
   function's class scope before installing it at the caller, or
3. Properly resolve the body's unqualified static-member
   references at template-instantiation time so the body stored
   in the symbol table is already fully resolved.

Each is a non-trivial restructuring of the constexpr-function
evaluation path; deferred to a future session.

### Status

cbmc-cpp regressions: 681/0/83 (two new tests added).
Dog-food unchanged at 20/17/80/0 (still dominated by Category-A
irept-body abandonment).

Total commits this session (so far): 7 source/test + 2 doc.
The branch is now 60+ commits ahead of
`tautschnig/cpp11-parser-rework-squashed`.


## 2026-05-27 (continued) Constexpr-eval-with-class-scope fix landed

Three commits implement the actual constexpr-eval-with-class-scope
fix referenced by the previous stop point.

### What landed

| commit | summary |
|---|---|
| `c25c5a6e9d` | Don't replace function symbol references with their bodies in make_constant |
| `dee70f78e0` | Mark constexpr member functions as is_macro for constexpr evaluation |
| `152785c8de` | Eagerly type-check constexpr method body in class scope before folding |

### Root cause

The earlier "symbol 'value' is unknown" cascade had three
intertwined defects:

1. **make_constant's symbol substitution treated function
   symbols like data symbols.**  In `c_typecheck_baset::make_constant`
   and `cpp_typecheckt::template_suffix`, a `visit_pre` traversal
   replaces every `symbol_exprt` with the symbol's `value` when
   the symbol is `is_macro` or `ID_C_constant`.  For data symbols
   that yields a constant.  For function symbols, whose `value`
   field IS the function body (a `code_blockt`) and whose
   `type.id()` is `ID_code`, it splices the BODY into the
   call's `function()` field — and any unresolved `cpp_name`
   nodes inside then get re-typechecked in the CALLER's scope,
   where class-scope members like a static `value` are not
   visible.

2. **Constexpr member methods were never marked `is_macro`.**
   `typecheck_compound_declarator` for non-virtual member
   functions calls `typecheck_member_function` which never
   propagates `storage_spec.is_constexpr()` from the
   declaration to the symbol's `is_macro` flag.  As a result
   the constexpr-function-call evaluator in
   `typecheck_side_effect_function_call` (which gates on
   `symbol_ptr->is_macro`) never saw constexpr methods as
   candidates and the buggy `make_constant` substitution
   above became the only "evaluator" — with the bug above as
   the consequence.

3. **The body wasn't type-checked at the moment of folding.**
   Template-class member bodies are queued by
   `add_method_body` and processed in `typecheck_method_bodies()`
   at the END of typechecking.  When a non-type template
   argument such as `gate<ic.get()>` needs constexpr-eval of
   `ic.get()` *during* typecheck, the body is still in
   parsed (cpp_name) form.  Even with the substitution bug
   above prevented, the constexpr-evaluator's parameter
   substitution + simplify produces an expression containing
   unresolved cpp_names which cannot be folded.

### The fixes

1. In both substitution sites, `if(node.type().id() == ID_code) return;`.

2. In `typecheck_compound_declarator`, after the non-virtual
   `typecheck_member_function` call, set `is_macro=true` on
   the freshly-created method symbol when
   `declaration.storage_spec().is_constexpr()`.

3. In the constexpr-eval block of
   `typecheck_side_effect_function_call`, when the called
   symbol is a class method whose body has not yet been
   type-checked AND the body contains at least one cpp_name
   AND the call's arguments are fully constant, eagerly call
   `convert_function(method_symbol)` so the body gets
   typechecked in the function's own (class) scope before
   the substitute-and-fold logic reads it.  Sets up the
   matching `template_map` from the class symbol's
   `C_template_arguments` first; saves/restores via
   `cpp_saved_template_mapt`.

The args-are-constant pre-guard in (3) is essential for
performance — without it, the eager typecheck cascades through
deeply-templated stdlib code such as `std::sort`'s comparator
family and OOMs in BMC.

### Test coverage

- `regression/cbmc-cpp/cpp17_constexpr_member_in_template`
  (new) covers the specific `integral_constant<bool, true>::get()`
  → `gate<ic.get()>` pattern.

### Status

cbmc-cpp regressions: 692/0/83 (one new test added).
Dog-food unchanged at 20/17/80/0.

`reserve_repro11.cpp` advances past the
`symbol 'value' is unknown` layer (the constexpr eval now
folds correctly) and stops at a different downstream issue:
an `expr2cpp::convert_struct` invariant violation
("component count mismatch") triggered while pretty-printing
some struct value during error formatting.  That is a
pre-existing pretty-print bug unrelated to constexpr eval —
deferred to a future session.

Total this session: 7 commits (6 source/test + 1 doc).


## 2026-05-27 (continued) Dog-food failure audit + partial std::pair fix

After the constexpr-eval-with-class-scope landing, dog-food
remained at 20/17/80/0.  Audited the 80 FAIL files to identify
shared root causes.

### Bucket distribution (80 FAIL files)

By first-error pattern:

| bucket | count | first error pattern |
|---|---|---|
| A | 22 | `instantiating 'sharing_treet'` |
| B | 18 | `symbol 'reserve' is unknown` |
| C | 8 | `instantiating 'std::basic_streambuf'` |
| D, E | 7 | `std::vector<dstringt>` / `std::unordered_map` |
| F | 2 | `std::optional` |
| G | 2 | `parse error` |
| H | 3 | `'X' is unknown (clear/read/...)` |
| I | 3 | `no match for symbol` |
| J | 3 | `does not uniquely resolve` |
| K | 2 | `invalid implicit conversion` |
| L | 1 | bare `CONVERSION ERROR` |
| misc | 9 | unique |

### Root cause: `std::pair<K, V>` does not elaborate

Buckets A, B, E, I, F (and pieces of D, J, H) — at least 47 of
80 failures — share a single root cause: `std::pair<K, V>` and
its base `std::__pair_base<K, V>` do not produce `tag-` symbols
when instantiated from libstdc++ headers.

Reproducible on a 6-line test:
```cpp
#include <utility>
int main() { std::pair<int, int> p; return 0; }
```

`--show-symbol-table` shows pair's nested types get tags (e.g.
`std::pair<...>::tag-__zero_as_null_pointer_constant`) but the
pair class itself does NOT.  CBMC reports VERIFICATION SUCCESSFUL
because `main()` collapses to a nondet stub when pair fails to
elaborate.

### First fix landed (2026-05-27 commit, partial)

Identified one of the underlying mechanisms via reduced repros.
`__pair_base` declares itself as a template-friend of `pair`,
and its destructor is private (default for `class`).  When
`pair`'s implicit destructor synthesis goes to call
`__pair_base::~__pair_base`, an access-check fallback in
`cpp_typecheck_resolve.cpp:resolve` had two defects that
prevented the derived-class-access path from matching:

1. The "current class" was taken as
   `current_scope().get_parent().identifier`, which is the
   ENCLOSING NAMESPACE when the resolution happens from a
   class scope directly (during destructor synthesis triggered
   by class elaboration).  The namespace symbol's
   `type.id() != ID_struct` so the loop never ran.  Walk the
   scope chain and pick the first class scope instead.
2. The expected base struct_tag identifier was built as
   `"tag-" + qualified_class_name` → e.g.
   `tag-std::__pair_base<...>`.  The actual stored
   identifier is `<namespace>::tag-<class_name>` →
   `std::tag-__pair_base<...>`.  Mismatched comparison.

With both fixed, a minimal pair-shaped test now elaborates:
```cpp
namespace ns {
  template<typename _T1, typename _T2> struct pair;
  template<typename U1, typename U2> class __pair_base {
    template<typename _T1, typename _T2> friend struct pair;
    ~__pair_base() = default;
    /* ... = delete operator= ... */
  };
  template<typename _T1, typename _T2>
  struct pair : public __pair_base<_T1, _T2> { /* first, second */ };
}
ns::pair<int, int> p;  // now creates tag-pair
```

Regression test `cpp17_private_base_dtor_via_friend` covers
this case.

### Why this didn't yet move dog-food

The fix unblocks the access-check pathway that fails in
`/tmp/`-located tests, but for files whose source location is
under `/usr/include/` (libstdc++), an EARLIER silent-bypass in
the same function sets `still_not_accessible = false` based on
the path, never reaching the buggy fallback.  So libstdc++'s
real `std::pair` instantiation still produces no tag — for a
DIFFERENT reason that has yet to be isolated.

The next investigation should:
1. Trace exactly where libstdc++'s pair elaboration aborts
   (despite the silent-bypass making access checks always
   succeed).  Possibly an earlier failure during template
   instantiation that sets `is_incomplete()` and prevents
   tag registration.
2. Test whether the issue is in `class_template_symbol`,
   in `elaborate_class_template`, or in
   `typecheck_compound_type` for pair specifically.

### Other shared root causes (smaller)

* **Bucket C (8 files)** — basic_streambuf SFINAE pollution
  followed by class-member access in `ieee_floatt::is_zero`.
* **~24 misc failures** — distinct one-off issues.

### Status

cbmc-cpp regressions: 693/0/83 (one new test added).
Dog-food unchanged at 20/17/80/0 — the access-check fix is
necessary but not sufficient for the libstdc++ pair issue.

Reproduction artifacts saved at `/tmp/std_dep_pair.cpp`,
`/tmp/std_dep_mypair.cpp`, `/tmp/just_pair.cpp`,
`/tmp/pair_min.cpp` (passes), `/tmp/reserve_min.cpp`.


## 2026-05-27 (continued) Pair instantiation deep dive: pinpointed the silent-throw chain

Continuing from the access-check fix, traced the libstdc++
`std::pair` elaboration silent-failure to a precise chain.

### The mechanism

1. `main()` body has `std::pair<int, int> p;`
2. `convert_function(main)` runs.  `typecheck_decl` on the
   declaration calls `typecheck_type(std::pair<int, int>)`.
3. That triggers `elaborate_class_template` →
   `instantiate_template(std::pair<int,int>)` →
   `convert_non_template_declaration` →
   `typecheck_compound_type` → `typecheck_compound_body`
   → `typecheck_compound_declarator` for some member of pair.
4. `typecheck_compound_declarator` calls `typecheck_type` on
   the member's type, which contains `pair<_U1, _U2>` (a
   template constructor's parameter type referencing the
   constructor's own template parameters, not the class's
   `_T1`, `_T2`).
5. Resolving `pair<_U1, _U2>` calls
   `disambiguate_template_classes` →
   `typecheck_template_args` → `typecheck_type` on `_U1` →
   `convert_template_parameter`.
6. `_U1` is not in `template_map` (the map has `_T1=int,
   _T2=int` from the class instantiation; the constructor
   template's own params aren't bound at this point).  
   `convert_template_parameter` does a SILENT `throw 0` (no
   error message, intended for SFINAE-style caller-recovery).
7. The throw propagates up to
   `typecheck_method_bodies`'s `catch(int)` for `main`.
   Because `had_template_instantiation=true`, the error is
   suppressed; main's body is left half-typechecked
   (`code(decl, sub=cpp_declaration{...})` for `p`).
8. Goto-conversion drops the un-typechecked `decl` statement
   silently → main becomes `SET RETURN VALUE 0` only.
9. `tag-std::pair<int,int>` IS created during instantiation,
   but with no consumer in main's goto code, it gets removed
   by `linking/remove_internal_symbols` as unused.

### Reproducing trace (by line 595 of `/usr/include/c++/13/bits/stl_pair.h`)

```cpp
template<typename _U1, typename _U2, typename
       enable_if<_PCCFP<_U1, _U2>::template
                   _ConstructiblePair<_U1, _U2>()
                 && !_PCCFP<_U1, _U2>::template
                   _ImplicitlyConvertiblePair<_U1, _U2>(),
                       bool>::type=false>
  explicit constexpr pair(const pair<_U1, _U2>& __p)  // ← throw fires here
```

This is a SFINAE-guarded template constructor.  Its parameter
type `pair<_U1, _U2>` references the constructor's own
template params.

### Why the typecheck_compound_declarator reached this path

The trace shows `typecheck_compound_declarator` on the stack
during pair's body elaboration.  `typecheck_compound_body`
dispatches based on `declaration.is_template()`:

- If template (constructor template), `convert_template_declaration`.
- Else, `typecheck_compound_declarator`.

Yet the stack has `typecheck_compound_declarator`.  Possible
causes (not isolated):
1. The constructor template's `is_template` bit isn't being
   set correctly for some declarations.
2. `convert_template_declaration` internally calls
   `typecheck_compound_declarator` on a substituted form
   without properly extending `template_map` first.

### Attempted fixes (all reverted)

1. **Return `template_parameter_symbol_type` instead of throwing
   in `convert_template_parameter`.**  Made the minimal repro
   `pair_min.cpp` work by leaving `_U1` unsubstituted, but
   triggered SIGABRT (invariant violations) in many existing
   regression tests that depend on the throw firing for SFINAE
   recovery.  Pre-existing throw is load-bearing.

2. **Save/restore `method_symbol.value` in `typecheck_method_bodies`'s
   suppress-on-template-instantiation catch.**  Doesn't help —
   the parsed-form `cpp_declaration` is still dropped by
   goto-conversion.

### Where the principled fix lives

The fix needs to ensure that when a constructor template's
signature is being typechecked during the parent class's body
elaboration, the constructor's OWN template parameters are
added to `template_map` as `template_parameter_symbol_type`
placeholders.  That requires changes to either:

- `convert_template_declaration` for function-template-in-class:
  populate `template_map` with the function template's params
  before calling typecheck_compound_declarator-equivalent.
- OR `typecheck_compound_body`: detect template members and
  set up the params correctly even on the non-template
  fallback path.

This is a non-trivial restructuring that risks the same
cascade of regressions seen with attempt #1.  Deferred.

### Status

cbmc-cpp regressions: 693/0/83.  Dog-food unchanged at
20/17/80/0.  No commits this iteration — the investigation
clarified the failure mechanism but did not produce a
non-regressing fix.

The line-595 `enable_if<_PCCFP<_U1, _U2>::...>` SFINAE pattern
is the smoking gun.  A future fix should either teach
`convert_template_parameter` to return an unsubstituted
`template_parameter_symbol_type` ONLY when the lookup happens
in a SFINAE context, or extend `template_map` with the inner
template's params when typechecking a member function template
signature inside a class template's body.

Reproduction artifacts saved at `/tmp/just_pair.cpp`,
`/tmp/pair_min.cpp` (the minimal pattern that DOES work
after the access-check fix from the previous iteration).
