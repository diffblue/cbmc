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
