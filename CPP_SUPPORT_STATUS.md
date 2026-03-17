# C++ Support Status — cpp11-parser-rework branch

Last updated: 2026-03-10 (session 20)

## C++11 — ~90% complete

### Working language features (~95%)
- `nullptr`, `auto`, `decltype`, `constexpr`, `static_assert`, `noexcept`
- Lambdas (capture by value/reference/init-capture), range-for, rvalue references, move semantics
- Variadic templates, parameter packs, `sizeof...` — **FIXED**: `sizeof...(args)` now works for expression packs
- Variadic template pack expansion with heterogeneous types — **FIXED**: each pack argument deduced individually
- `enum class`, delegating constructors, `override`/`final`
- `thread_local`, `char16_t`/`char32_t`, user-defined literals (numeric and string)
- Template aliases, trailing return types, inline namespaces
- Default template arguments for function templates — **FIXED**: `template<typename T = int> T f()` works
- Brace initialization, `= default`, `= delete`, return with braces
- `noexcept` operator (`noexcept(expr)`)
- `alignof` operator
- `alignas` specifier on struct/class/union — **FIXED**: `struct alignas(16) S` works
- Explicit conversion operators (`explicit operator bool()`)
- `static constexpr auto` member type deduction — **FIXED**: auto deduced from initializer
- Perfect forwarding with rvalue references
- SFINAE with `enable_if` — **FIXED**: alternative overloads stored in side map, tried on primary SFINAE failure
- Default member initializers (NSDMI) — **FIXED**: applied during both POD default construction and non-POD constructor initialization
- Range-for over braced initializer lists (`for(int x : {1,2,3})`) — **FIXED**
- Raw string literals (`R"delim(content)delim"`) — **FIXED**: all encoding prefixes supported
- Namespace alias in block scope (`namespace X = Y::Z;` inside functions) — **FIXED**

### STL/library support (~60%)
- `std::vector`, `std::map`, `std::string`, `std::list`, `std::set`, `std::deque` — basic operations work but many member functions produce "no body" stubs
- `std::array`, `std::tuple` — basic usage works (but `std::array` aggregate init loses main() body)
- `std::thread`, `std::mutex`, `std::chrono` — headers parse
- `std::unique_ptr` — no body for main() due to template constructor failure
- `std::shared_ptr` — invariant violation in cpp_constructor.cpp
- `std::function` — no body for main() due to template constructor failure
- `std::regex` — times out during type-checking
- `std::initializer_list` — **FIXED**: brace-init-list `{1,2,3}` converts to `std::initializer_list<T>` for function arguments and constructors
- `std::string` — basic operations work but `_M_construct` (iterator version) has no body
- `std::vector` — basic operations work but `emplace_back` and `_Destroy_aux::__destroy` have no body

### Known gaps
- Complex STL template instantiations often fail or produce stubs
- Template method symbol collision with different return types — **FIXED**: `template<T> static T test(int)` instantiated with different types no longer collides; fixes `std::common_type` with multiple instantiations
- `std::initializer_list` as function argument (`sum({1,2,3})`) — **FIXED**: brace-init-list to `std::initializer_list<T>` conversion
- Inheriting constructors (`using Base::Base`) — **FIXED**: base class constructors imported into derived class
- Variadic template pack expansion in recursive functions — **FIXED**: pack parameters expanded to N copies
- Lambda returning a lambda — inner lambda symbol removed as unused (KNOWNBUG: `cpp11_lambda_returning_lambda`)
- Constexpr member function call on constexpr variable — **FIXED**: constexpr struct variables kept as symbols for this-pointer formation
- Nested member template instantiation (`Outer<int>::Inner<double>`) — **FIXED**: outer template parameters now available during inner template instantiation
- Trailing return type with `decltype(a+b)` — **FIXED**: parameters put in scope for both non-template and template functions
- `decltype(f())` preserving reference types — **FIXED**: `decltype` now recovers reference type from implicitly dereferenced expressions

---

## C++14 — ~90% complete

### Working language features (~95%)
- Binary literals (`0b1010`)
- Digit separators (`1'000'000`) — **FIXED**: apostrophes stripped from integer literals
- `decltype(auto)` — value case works; reference case (parenthesized return) — **FIXED**: deduces `int&` for `return (x)` and for function calls returning references
- Variable templates — **FIXED**: constexpr value now correctly substituted
- Relaxed `constexpr` (loops, local variables)
- Recursive `constexpr` functions with ternary operator — **FIXED**
- `constexpr` classes with constructors and member functions — **FIXED**
- Auto return type deduction in free functions and member functions — **FIXED**
- `[[deprecated]]` attribute
- Generic lambdas (`[](auto x){}`) — **FIXED**: auto params replaced with int
- Lambda init-capture (`[y = expr](){}`) — **FIXED**

### STL/library support (~60%)
- Same as C++11

### Known gaps
- Generic lambdas — **FIXED**: work with any argument type (struct, double, etc.)
- `decltype(auto)` returning reference via function call — **FIXED**
- Non-type variadic template parameters (`template<int... Is>`) — **FIXED**: ellipsis flag preserved after rDeclarator
- Template alias not expanded during function template argument deduction — **FIXED**: aliases expanded before deduction

---

## C++17 — ~75% complete

### Working language features (~80%)
- `if constexpr` (in templates and non-templates) — **FIXED**: discarded branch not typechecked, enabling type-dependent code in branches
- `if constexpr` with `auto` return type — **FIXED**: deferred return type deduction when discarded branch has ill-formed code
- Structured bindings (`auto [x,y] = s`) — including tuple-like protocol
- Structured bindings with references (`auto& [a,b] = s`) — **FIXED**: modifications through bindings affect original
- Nested namespaces (`namespace A::B {}`)
- Inline variables (`static inline int x = 42`)
- `noexcept` as part of the type system
- Constexpr lambdas — **FIXED**: `constexpr`/`consteval` after parameter list
- `[[nodiscard]]`, `[[maybe_unused]]`, `[[fallthrough]]`
- `if`/`switch` with initializer (`if(int x=42; x>0)`)
- `if` with initializer and structured bindings (`if(auto [a,b] = expr; cond)`) — **FIXED**
- Class template argument deduction (CTAD) — **FIXED**: basic and multi-argument cases work
- `template<auto>` — **FIXED**: non-type template parameter with auto type
- `static_assert` without message
- Scoped enum with underlying type (`enum class byte : unsigned char {}`)
- Direct-list-initialization of scoped enums (`byte{42}`) — **FIXED**
- Optional-like template patterns

### STL/library support (~55%)
- `std::optional` — mostly works
- `std::any` — works
- `std::string_view` — **FIXED**: works with verification (size(), operator[])
- `std::variant` — parses but type-checking errors (namespace alias and using-pack fixes unblocked parsing; `_Nth_type` fixed by partial specialization empty pack matching; fold expression in `_Traits` **FIXED** by class body fold expansion; void-typed member **FIXED** by skipping during instantiation; remaining: type mismatch in symex_assign)
- `std::filesystem` — type-checking errors on system header
- Good coverage for: vector, deque, algorithm, string, memory, tuple, iterator, numeric, valarray, functional

### Known gaps — language
- **Fold expressions** (`(args + ...)` and `(... && args)`) — **FIXED**: right, left, and binary folds for all binary operators (+, -, *, /, %, |, ^, &, &&, ||, comma); also expanded in class template member initializers
- **Deduction guides** — **FIXED**: silently skipped, CTAD handles deduction
- **Using-declaration pack expansion** (`using Base::member...;`) — **FIXED**: parsed and skipped
- **C-style variadic lambda parameters** (`[](int x, ...) {}`) — **FIXED**
- **CTAD with aggregates and deduction guides** — **FIXED**: brace-init CTAD now works
- **Variadic template bases** (`struct D : Bases...`) — **FIXED**: base classes expanded during class template instantiation

---

## C++20 — ~40% complete

### Working language features (~50%)
- `char8_t` (as unsigned char), `u8` character literals
- `constinit` (treated as constexpr)
- `consteval` (treated as constexpr)
- `if consteval` — **FIXED**: takes runtime (else) branch since CBMC performs runtime verification via symbolic execution
- Designated initializers (`{.x=1, .y=2}`)
- `<=>` spaceship operator — **FIXED**: both user-defined and built-in on primitives
- Three-way comparison with `std::strong_ordering` — **FIXED**: self-referential static member crash resolved
- `concept` declarations (`template<T> concept Name = expr`)
- Concept-constrained template parameters (`template<Integral T>`) — **FIXED**: also supports `Concept<Args> T` and qualified `ns::Concept T`
- `requires` clauses — **FIXED**: leading and trailing (including on constructors), parenthesized and unparenthesized, compound expressions with `&&`/`||`, `requires requires(...)` pattern, built-in type traits
- `requires` expressions — **FIXED**: `requires(T a, T b) { a + b; }` parsed as `true`
- Constrained `auto` — **FIXED**: `Concept auto x = 42` works
- `co_return`/`co_await`/`co_yield` (parsed as stubs — no coroutine semantics)
- Template lambdas `[]<typename T>` — **FIXED**: instantiated at call site with actual types
- `using enum` — **FIXED**: enumerators imported into scope
- Aggregate initialization with parentheses — **FIXED**: `S s(1, 2)` for aggregates
- Aggregate initialization with base classes — **FIXED**: `Derived d{{10}, 20}` for structs with bases
- Function contracts `pre(expr)` / `post(name: expr)` (stored as CPROVER annotations)
- `[[no_unique_address]]` — works (attribute ignored, which is correct for verification)
- Range-based for with init-statement (`for(init; decl : range)`) — **FIXED**
- `constexpr` virtual functions — works (virtual dispatch at runtime)
- `constexpr` dynamic allocation (`new`/`delete` in constexpr) — works
- Floating-point non-type template parameters — **FIXED**: `template<double D>` works

### STL/library support (~30%)
- `<concepts>` — **FIXED**: parses and type-checks successfully
- `<compare>` — **FIXED**: parses and type-checks successfully (all three ordering types)
- `<span>` — **FIXED**: parses and type-checks successfully
- `<ranges>` — parse errors fixed, but crashes in merge_type during type-checking
- `<utility>` in C++20 — **FIXED**: works (was blocked by `<compare>`)
- `<numbers>` — works
- `<bit>` — works
- `<format>`, `<coroutine>` — parse errors / type-checking errors (KNOWNBUG tests added)

### Known gaps — language
- **Abbreviated function templates** (`auto f(auto x)`) — **FIXED**: auto params synthesize template type params
- **Template lambda instantiation** — **FIXED**: template lambda params treated like generic lambda auto params
- **Modules** — no `import`/`export` parsing at all
- **`explicit(bool)`** — **FIXED**: depth-counted to handle template-ids in expression
- **`noexcept(expr)` with template-ids** — **FIXED**: depth-counted to handle `<>` in expression
- **Friend constexpr function access** — **FIXED**: disable access control during friend body type-checking
- **Defaulted friend operator==** — **FIXED**: `= default` replaced with empty block; body generated with correct parameter names for friend functions
- **Coroutine semantics** — keywords parsed as no-ops; no promise_type resolution
- **Three-way comparison categories** (`std::strong_ordering` etc.) — **FIXED**: works with user-defined types
- **`constexpr` containers** — not modeled
- **Class type NTTP** (`template<Fixed F>`) — KNOWNBUG: "expected type, but got expression"
- **Defaulted three-way comparison** (`auto operator<=>(const T&) const = default`) — **FIXED**: generates member-wise comparison body
- **Defaulted equality** (`bool operator==(const T&) const = default`) — **FIXED**: generates member-wise equality body
- **Relational operators from `<=>`** — **FIXED**: `<`, `>`, `<=`, `>=` synthesized from `<=>` by rewriting as `(a <=> b) < 0`
- **Synthesized `operator!=`** — **FIXED**: `a != b` rewritten as `!(a == b)` when no explicit `operator!=` exists
- **Constexpr eval of deferred functions** — **FIXED**: skip constexpr evaluation when function body not yet type-checked
- **Ternary in template default args with enum types** — **FIXED**: enum tags registered in parser scope; `?` allowed after template arguments
- **Concept expressions** — **FIXED**: concepts can be used as boolean expressions (e.g., `bool b = C<int>;`, `if constexpr(C<T>)`)
- **Lambda init-capture with pack expansion** (`[...x = args]`) — **FIXED**: parsed and expanded during template instantiation
- **Bitfield default member initializers** (`unsigned x:1 = 0`) — **FIXED**: use conditional expression for bitfield width
- **`__builtin_is_constant_evaluated()`** — **FIXED**: returns false (CBMC evaluates at runtime)
- **`__is_trivially_constructible` and related traits** — **FIXED**: `__is_trivially_constructible`, `__is_nothrow_constructible`, `__is_trivially_assignable`, `__is_nothrow_assignable` now handled
- **Constrained partial specializations** — **FIXED**: duplicate bodies downgraded to warning for partial specializations
- **Pack expansion in braced member initializers** — **FIXED**: `val{static_cast<Args&&>(args)...}` now parses

---

## C++23 — ~25% complete

### Working language features (~35%)
- `uz`/`UZ` size_t literal suffix
- `if consteval` — **FIXED**: takes runtime (else) branch (see C++20)
- Deducing this — **FIXED**: `s.get()` dispatches to `int get(this S self)`
- Multidimensional `operator[]` — **FIXED**: `m[i,j]` syntax works in C++23 mode
- `static operator()` — works
- `static operator[]` — works
- `auto(x)` decay copy — **FIXED**: `auto b = auto(a)` works
- `#warning` preprocessor directive — works
- `#elifdef` / `#elifndef` — works

### Known gaps — language
- **Lambda in unevaluated contexts** — **FIXED**: `decltype([]{})` works; lambda address stored as type annotation for default-initialization
- **Explicit object parameters in lambdas** — **FIXED**: `[](this auto self, int a, int b)` works
- **`std::expected`**, **`std::mdspan`**, **`std::print`**, **`std::stacktrace`** — no library modeling
- **`constexpr` for `<cmath>`/`<cstdlib>`** — not modeled

---

## C++26 — ~10% complete

### Working language features (~10%)
- `= delete("message")` — parses and discards the message string
- Pack indexing `Ts...[0]` — **FIXED**: resolves during template argument substitution
- Function contracts `pre(expr)` / `post(name: expr)` — parsed and stored

### Known gaps — language
- **Reflection** (`^`, `[:..:]`) — not started
- **Pattern matching** — not started
- **`std::execution`** (sender/receiver) — not started
- **Contracts semantics** — parsed but verification integration is minimal
- **Trivial relocatability** — not started
- **`constexpr` placement new** — not supported

---

## Summary table

| Standard | Language features | STL/Library | Overall |
|----------|------------------|-------------|---------|
| C++11    | ~95%             | ~60%        | ~90%    |
| C++14    | ~95%             | ~60%        | ~90%    |
| C++17    | ~80%             | ~55%        | ~75%    |
| C++20    | ~55%             | ~30%        | ~45%    |
| C++23    | ~35%             | ~0%         | ~25%    |
| C++26    | ~15%             | ~0%         | ~10%    |

## Systemic gaps across all standards

1. **STL library modeling** — CBMC parses system headers but many complex template instantiations fail or produce stubs with "no body" warnings. This affects every standard.
2. **Template metaprogramming depth** — complex SFINAE, fold expressions, and concept constraints hit limits in the type-checker.
3. **C++20+ is partially stubbed** — the parser accepts most syntax but semantic support (coroutine state machines, concept constraint checking, module system) is incomplete.
4. **`__builtin_strlen`** — **FIXED**: library model added, enables `std::string_view` verification.
5. **`__builtin_is_constant_evaluated`** — **FIXED**: returns false in C++ type-checker.
6. **Struct zero-initialization with type aliases** — **FIXED**: type alias components (e.g., `using is_transparent = void;`) now skipped during zero-init.
7. **Template instantiation with unresolved args** — **FIXED**: `class_template_symbol` returns template symbol instead of crashing.
8. **`operator()` on temporary objects** — **FIXED**: temporary wrapped in `temporary_object` side effect for this-pointer formation.
9. **Precondition instrumentation crash** — **FIXED**: skip `actuals_replace_map` when no preconditions, avoiding namespace lookup crash for missing destructor symbols.
10. **Partial specialization with empty variadic packs** — **FIXED**: partial specialization matching now allows trailing pack expansion args to match zero elements; pack expansion ellipsis preserved in `rTypeName`.
11. **Missing GCC built-in type predicates** — **FIXED**: added `__is_layout_compatible`, `__is_nothrow_convertible`, `__is_pointer_interconvertible_base_of` to scanner and type-checker. These are used in libstdc++ headers when `__has_builtin` evaluates to true on GCC 13.

## KNOWNBUG tests (documented gaps)

| Test | Standard | Issue |
|------|----------|-------|
| `cpp11_initializer_list_arg` | C++11 | **FIXED**: brace-init-list to `std::initializer_list<T>` conversion |
| `cpp11_template_template_deduction` | C++11 | **FIXED**: template template parameter deduction |
| `cpp11_trailing_decltype` | C++11 | **FIXED**: trailing return `decltype(a+b)` — params in scope |
| `cpp11_variadic_expansion` | C++11 | **FIXED**: variadic pack expansion in function body |
| `cpp11_variadic_mixed_types` | C++11 | **FIXED**: variadic pack with heterogeneous types deduced individually |
| `cpp11_lambda_returning_lambda` | C++11 | **FIXED**: lambda returning lambda |
| `cpp11_partial_ordering` | C++11 | **FIXED**: partial ordering of template specializations |
| `cpp11_sfinae_default_arg` | C++11 | **FIXED**: SFINAE with `enable_if` as default template argument |
| `cpp11_recursive_template_depth` | C++11 | **FIXED**: converging integer args allow deeper recursion |
| `cpp11_template_method_outside` | C++11 | **FIXED**: template method defined outside non-template class |
| `cpp11_trailing_decltype_template` | C++11 | **FIXED**: trailing `decltype(a+b)` in function templates |
| `cpp11_template_alias_deduction` | C++11 | **FIXED**: Template alias expanded during function template argument deduction |
| `cpp14_index_sequence` | C++14 | **FIXED**: non-type variadic template parameter packs |
| `cpp14_decltype_auto_ref` | C++14 | **FIXED**: `decltype(auto)` deduces reference from function returning ref |
| `cpp17_fold_expr` | C++17 | **FIXED**: fold expressions expanded during template instantiation |
| `cpp17_fold_comma` | C++17 | **FIXED**: comma operator in fold expressions |
| `cpp17_variadic_bases` | C++17 | **FIXED**: variadic base classes expanded during class template instantiation |
| `cpp20_lambda_unevaluated` | C++20 | **FIXED**: Lambda in unevaluated context (decltype) |
| `cpp20_nttp_string` | C++20 | Class type as non-type template parameter |
| `cpp20_ternary_template_default` | C++20 | **FIXED**: merge_type crash with empty type |
| `cpp20_coroutine_header` | C++20 | `<coroutine>` header: auto return type deduction in operator<=> |
| `cpp20_format_header` | C++20 | `<format>` header: parse errors |
| `cpp17_optional_has_value` | C++17 | std::optional has_value(): no body for main() |
| `cpp11_temp_operator_call` | C++11 | **FIXED**: operator() on temporary object |
| `cpp17_variant_basic` | C++17 | std::variant: _Nth_type fixed, but no body for main() |
| `cpp20_lambda_pack_capture` | C++20 | **FIXED**: Lambda init-capture with pack expansion |
| `cpp26_pack_indexing` | C++26 | **FIXED**: Pack indexing instantiation |
| `cpp11_array_init` | C++11 | std::array: no body for main() |
| `cpp11_function_basic` | C++11 | std::function: no body for main() |
| `cpp11_string_basic` | C++11 | std::string: _M_construct has no body |
| `cpp11_vector_push_back` | C++11 | std::vector: emplace_back has no body |
| `cpp14_unique_ptr_basic` | C++14 | std::unique_ptr: no body for main() |
| `cpp20_ranges_basic` | C++20 | `<ranges>`: template struct defined previously |
| `cpp23_expected_basic` | C++23 | `<expected>`: template struct defined previously |

## Key file locations

- **Scanner**: `src/ansi-c/scanner.l`
- **Parser tokens**: `src/ansi-c/parser.y`
- **C++ parser**: `src/cpp/parse.cpp` (~9600 lines, hand-written recursive descent)
- **C++ type-checker**: `src/cpp/cpp_typecheck*.cpp`
- **C type-checker (base)**: `src/ansi-c/c_typecheck*.cpp`
- **Config/standards**: `src/util/config.h`, `src/util/config.cpp`
- **Scanner state flags**: `src/ansi-c/ansi_c_parser.h` (`cpp98`, `cpp11`, `cpp20`)
- **IREP IDs**: `src/util/irep_ids.def`
- **Goto conversion**: `src/goto-programs/goto_convert*.cpp`
- **Symbolic execution**: `src/goto-symex/`

## Test locations

- `regression/cbmc-cpp/` — 340+ tests (main C++ regression suite)
- `regression/cpp/` — 243 tests (parser/type-checker focused, all CORE pass with goto-cc)
- `regression/systemc/` — 27 tests
- Tests prefixed `cpp11_`, `cpp14_`, `cpp17_`, `cpp20_`, `cpp23_`, `cpp26_`
