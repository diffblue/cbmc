# C++ Support Status — cpp11-parser-rework branch

Last updated: 2026-03-07

## C++11 — ~90% complete

### Working language features (~95%)
- `nullptr`, `auto`, `decltype`, `constexpr`, `static_assert`, `noexcept`
- Lambdas (capture by value/reference), range-for, rvalue references, move semantics
- Variadic templates, parameter packs, `sizeof...` — **FIXED**: `sizeof...(args)` now works for expression packs
- `enum class`, delegating constructors, `override`/`final`
- `thread_local`, `char16_t`/`char32_t`, user-defined literals
- Template aliases, trailing return types, inline namespaces
- Brace initialization, `= default`, `= delete`
- `noexcept` operator (`noexcept(expr)`)
- `alignof` operator
- Explicit conversion operators (`explicit operator bool()`)
- Perfect forwarding with rvalue references
- SFINAE with `enable_if`
- Range-for over braced initializer lists (`for(int x : {1,2,3})`) — **FIXED**

### STL/library support (~60%)
- `std::vector`, `std::map`, `std::string`, `std::list`, `std::set`, `std::deque` — basic operations work but many member functions produce "no body" stubs
- `std::array`, `std::tuple` — basic usage works
- `std::thread`, `std::mutex`, `std::chrono` — headers parse
- `std::unique_ptr` — partial (verification failures)
- `std::shared_ptr` — crashes
- `std::function` — crashes
- `std::regex` — times out during type-checking
- `std::initializer_list` — parses but goto-conversion issues with brace-init arguments

### Known gaps
- Complex STL template instantiations often fail or produce stubs
- `std::initializer_list` as function argument (`sum({1,2,3})`) produces "no body for main" (KNOWNBUG test: `cpp11_initializer_list_arg`)
- Inheriting constructors (`using Base::Base`) — conversion error
- Raw string literals (`R"(...)"`) — not parsed
- Variadic template pack expansion in recursive functions — only last arg passed

---

## C++14 — ~90% complete

### Working language features (~95%)
- Binary literals (`0b1010`)
- Digit separators (`1'000'000`) — **FIXED**: apostrophes stripped from integer literals
- `decltype(auto)` — value case works; reference case (parenthesized return) is KNOWNBUG
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
- Generic lambdas only work when called with `int` arguments (auto→int approximation)
- `decltype(auto)` returning reference via parenthesized expression — KNOWNBUG
- Non-type variadic template parameters (`template<int... Is>`) — too many template args error

---

## C++17 — ~75% complete

### Working language features (~80%)
- `if constexpr` (in templates and non-templates)
- Structured bindings (`auto [x,y] = s`) — including tuple-like protocol
- Nested namespaces (`namespace A::B {}`)
- Inline variables (`static inline int x = 42`)
- `noexcept` as part of the type system
- Constexpr lambdas — **FIXED**: `constexpr`/`consteval` after parameter list
- `[[nodiscard]]`, `[[maybe_unused]]`, `[[fallthrough]]`
- `if`/`switch` with initializer (`if(int x=42; x>0)`)
- Class template argument deduction (CTAD) — **FIXED**: basic cases work
- `template<auto>` — **FIXED**: non-type template parameter with auto type
- `static_assert` without message
- Scoped enum with underlying type (`enum class byte : unsigned char {}`)
- Optional-like template patterns

### STL/library support (~50%)
- `std::optional` — mostly works
- `std::any` — works
- `std::string_view` — parses but verification failures
- `std::variant` — PARSING ERROR on system header
- `std::filesystem` — type-checking errors on system header
- Good coverage for: vector, deque, algorithm, string, memory, tuple, iterator, numeric, valarray, functional

### Known gaps — language
- **Fold expressions** (`(args + ...)`) — parse but "no body" errors; incomplete template instantiation (KNOWNBUG: `cpp17_fold_expr`)
- **Deduction guides** — **FIXED**: silently skipped, CTAD handles deduction
- **CTAD with aggregates and deduction guides** — KNOWNBUG: multi-param template deduction
- **Variadic template bases** (`struct D : Bases...`) — KNOWNBUG

---

## C++20 — ~40% complete

### Working language features (~50%)
- `char8_t` (as unsigned char), `u8` character literals
- `constinit` (treated as constexpr)
- `consteval` (treated as constexpr)
- `if consteval` (always takes runtime/else branch)
- Designated initializers (`{.x=1, .y=2}`)
- `<=>` spaceship operator — **FIXED**: both user-defined and built-in on primitives
- Three-way comparison with `std::strong_ordering` — **FIXED**: self-referential static member crash resolved
- `concept` declarations (`template<T> concept Name = expr`)
- Concept-constrained template parameters (`template<Integral T>`)
- `requires` clauses — **FIXED**: both leading and trailing, with concept names (`requires Addable<T>`)
- `requires` expressions — **FIXED**: `requires(T a, T b) { a + b; }` parsed as `true`
- Constrained `auto` — **FIXED**: `Concept auto x = 42` works
- `co_return`/`co_await`/`co_yield` (parsed as stubs — no coroutine semantics)
- Template lambdas `[]<typename T>` (template params skipped, not instantiated)
- `using enum` — **FIXED**: enumerators imported into scope
- Aggregate initialization with parentheses — **FIXED**: `S s(1, 2)` for aggregates
- Function contracts `pre(expr)` / `post(name: expr)` (stored as CPROVER annotations)
- `[[no_unique_address]]` — works (attribute ignored, which is correct for verification)
- `constexpr` virtual functions — works (virtual dispatch at runtime)
- `constexpr` dynamic allocation (`new`/`delete` in constexpr) — works

### STL/library support (~5%)
- Most C++20 library features not modeled
- `<ranges>`, `<span>`, `<format>`, `<coroutine>` — system headers fail to parse

### Known gaps — language
- **Abbreviated function templates** (`auto f(auto x)`) — **FIXED**: auto params synthesize template type params
- **Template lambda instantiation** — **FIXED**: template lambda params treated like generic lambda auto params
- **Modules** — no `import`/`export` parsing at all
- **Coroutine semantics** — keywords parsed as no-ops; no promise_type resolution
- **Three-way comparison categories** (`std::strong_ordering` etc.) — **FIXED**: works with user-defined types
- **`constexpr` containers** — not modeled
- **Class type NTTP** (`template<Fixed F>`) — KNOWNBUG: "expected type, but got expression"

---

## C++23 — ~25% complete

### Working language features (~35%)
- `uz`/`UZ` size_t literal suffix
- `if consteval` (same as C++20 support)
- Deducing this — **FIXED**: `s.get()` dispatches to `int get(this S self)`
- Multidimensional `operator[]` — **FIXED**: `m[i,j]` syntax works in C++23 mode
- `static operator()` — works
- `static operator[]` — works
- `auto(x)` decay copy — **FIXED**: `auto b = auto(a)` works
- `#warning` preprocessor directive — works
- `#elifdef` / `#elifndef` — works

### Known gaps — language
- **Lambda in unevaluated contexts** — `decltype([]{})` works for simple cases
- **Explicit object parameters in lambdas** — KNOWNBUG: wrong number of arguments
- **`std::expected`**, **`std::mdspan`**, **`std::print`**, **`std::stacktrace`** — no library modeling
- **`constexpr` for `<cmath>`/`<cstdlib>`** — not modeled

---

## C++26 — ~5% complete

### Working language features (~10%)
- `= delete("message")` — parses and discards the message string
- Pack indexing `Ts...[0]` — parses but doesn't instantiate the indexed type
- Function contracts `pre(expr)` / `post(name: expr)` — parsed and stored

### Known gaps — language
- **Pack indexing instantiation** — `Ts...[0]` doesn't resolve during template argument substitution
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
| C++17    | ~80%             | ~50%        | ~75%    |
| C++20    | ~50%             | ~5%         | ~40%    |
| C++23    | ~35%             | ~0%         | ~25%    |
| C++26    | ~10%             | ~0%         | ~5%     |

## Systemic gaps across all standards

1. **STL library modeling** — CBMC parses system headers but many complex template instantiations fail or produce stubs with "no body" warnings. This affects every standard.
2. **Template metaprogramming depth** — complex SFINAE, fold expressions, and concept constraints hit limits in the type-checker.
3. **C++20+ is partially stubbed** — the parser accepts most syntax but semantic support (coroutine state machines, concept constraint checking, module system) is incomplete.

## KNOWNBUG tests (documented gaps)

| Test | Standard | Issue |
|------|----------|-------|
| `cpp11_initializer_list_arg` | C++11 | `{1,2,3}` as function arg → no body for main |
| `cpp11_template_template_deduction` | C++11 | Template template parameter deduction fails |
| `cpp11_variadic_expansion` | C++11 | Variadic pack expansion only passes last arg |
| `cpp11_inheriting_ctor` | C++11 | Inheriting constructors → conversion error |
| `cpp11_raw_string_literal` | C++11 | Raw string literals not parsed |
| `cpp14_decltype_auto_ref` | C++14 | `decltype(auto)` returning reference → not an lvalue |
| `cpp14_index_sequence` | C++14 | Non-type variadic template parameters |
| `cpp17_fold_expr` | C++17 | Fold expressions need variadic pack expansion |
| `cpp17_ctad_aggregate` | C++17 | CTAD with aggregate + deduction guide |
| `cpp17_variadic_bases` | C++17 | Variadic template base classes |
| `cpp20_nttp_string` | C++20 | Class type as non-type template parameter |
| `cpp23_deducing_this_lambda` | C++23 | Explicit object parameter in lambda |
| `cpp26_pack_indexing` | C++26 | Pack indexing instantiation |

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
- `regression/cpp/` — 243 tests (parser/type-checker focused)
- `regression/systemc/` — 27 tests
- Tests prefixed `cpp11_`, `cpp14_`, `cpp17_`, `cpp20_`, `cpp23_`, `cpp26_`
