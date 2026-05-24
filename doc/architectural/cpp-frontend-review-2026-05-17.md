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
