# CBMC C++ Standard Support Status

**Date:** 2026-03-15
**Branch:** `cpp11-parser-rework`
**Compiler:** g++ 13 (libstdc++)
**Tests:** 278 CORE, 1 KNOWNBUG

## Summary

| Standard | Language | Library | Tests | Overall |
|----------|----------|---------|-------|---------|
| C++11    | ★★★★★   | ★★★★☆  | 106+1 | ~95%    |
| C++14    | ★★★★★   | ★★★★★  | 21    | ~98%    |
| C++17    | ★★★★★   | ★★★★☆  | 58    | ~93%    |
| C++20    | ★★★★☆   | ★★★★☆  | 68    | ~85%    |
| C++23    | ★★★★☆   | ★★☆☆☆  | 21    | ~50%    |
| C++26    | ★★☆☆☆   | ★☆☆☆☆  | 4     | ~20%    |

---

## C++11

**106 CORE tests, 1 KNOWNBUG.**

### Language Features — all working
- `auto`, `decltype`, `decltype(auto)`
- Range-based `for` (including over braced-init-lists)
- `nullptr`, scoped enums (`enum class`)
- `constexpr` functions and variables
- Lambda expressions (capture by value/reference/init-capture)
- Rvalue references, move semantics, perfect forwarding
- Variadic templates, parameter packs, `sizeof...`
- Template aliases (`using`), trailing return types
- `static_assert`, `noexcept` (specifier and operator)
- `alignas`, `alignof`
- User-defined literals (numeric, string, standard library suffixes)
- Delegating constructors, inheriting constructors
- Default member initializers (NSDMI)
- `= default`, `= delete`
- Inline namespaces
- Raw string literals
- Explicit conversion operators
- SFINAE with `enable_if`
- Braced-init-list with `auto` (modeled as array; `std::initializer_list<T>.size()` also works)

### Standard Library
| Header | Parse | Verify | Notes |
|--------|-------|--------|-------|
| `<string>` | ✅ | ✅ `s.size()==5` verified | `_M_construct` body provided via template method fix |
| `<vector>` | ✅ | ✅ `v[0]==42` verified | `emplace_back` body provided; `operator new/delete` modeled |
| `<map>` | ✅ | ✅ verified with `--unwind` | |
| `<set>`, `<list>`, `<deque>` | ✅ | ✅ | |
| `<array>` | ✅ | ✅ `a.size()==3` verified | |
| `<tuple>` | ✅ | ✅ `get<0>(t)==1` verified | |
| `<unordered_map>`, `<unordered_set>` | ✅ | ✅ | |
| `<memory>` | ✅ | ✅ `unique_ptr`, `shared_ptr`, `make_shared` all verified | |
| `<functional>` | ✅ | ✅ `std::function` verified | |
| `<algorithm>`, `<numeric>` | ✅ | ✅ | |
| `<chrono>` | ✅ | ✅ | |
| `<thread>`, `<mutex>`, `<condition_variable>`, `<future>` | ✅ | ✅ | |
| `<atomic>` | ✅ | ✅ | |
| `<iostream>`, `<fstream>`, `<sstream>` | ✅ | ✅ | |
| `<regex>` | ✅ parses | ❌ operations have no body | `_Scanner` class body fails silently |

### KNOWNBUG
- `cpp11_regex_match`: `std::regex_match` returns nondeterministic value because `_Scanner` class template body processing fails in the system header.

---

## C++14

**21 CORE tests, 0 KNOWNBUG.**

### Language Features — all working
- Generic lambdas (`auto` parameters)
- Return type deduction
- Binary literals (`0b1010`), digit separators (`1'000`)
- Variable templates
- Relaxed `constexpr` (loops, local variables)
- `decltype(auto)` (value and reference cases)
- `[[deprecated]]` attribute
- Lambda init-capture

### Standard Library
All C++11 library support carries forward. `std::make_unique` works.

---

## C++17

**58 CORE tests, 0 KNOWNBUG.**

### Language Features — all working
- Structured bindings (including references, tuple-like protocol)
- `if`/`switch` with initializer
- `if constexpr`
- Fold expressions (all binary operators, left/right/binary folds)
- Inline variables
- Nested namespaces (`A::B::C`)
- Class template argument deduction (CTAD)
- `template<auto>` non-type template parameters
- `static_assert` without message
- `[[nodiscard]]`, `[[maybe_unused]]`, `[[fallthrough]]`
- Deduction guides (silently skipped; CTAD handles deduction)
- `constexpr` lambdas

### Standard Library
| Header | Parse | Verify | Notes |
|--------|-------|--------|-------|
| `<string_view>` | ✅ | ✅ | |
| `<optional>` | ✅ | ✅ `has_value()` verified | |
| `<variant>` | ✅ | ✅ `get<T>(v)` verified | |
| `<any>` | ✅ | ✅ | |
| `<filesystem>` | ✅ parses | ⚠️ `path` constructors incomplete | Class body partially registered |
| `<charconv>` | ✅ | ✅ | |

---

## C++20

**68 CORE tests, 0 KNOWNBUG.**

### Language Features — all working
- Concepts (`concept` declarations, `requires` clauses and expressions)
- Shorthand concept constraints (`template<std::integral T>`) — including qualified names
- Concept subsumption ordering
- Three-way comparison (`<=>`) with `std::strong_ordering`
- Designated initializers
- `consteval`, `constinit`
- `if consteval` / `if !consteval`
- Abbreviated function templates (`auto` parameters)
- `co_return` (basic coroutine support — parsed as simplified control flow)
- Class type NTTP with brace initialization (`get<Fixed{42}>()`)
- Template lambdas (`[]<typename T>`)
- `using enum`
- Aggregate initialization with parentheses and base classes
- Range-based for with init-statement
- `constexpr` virtual functions, dynamic allocation
- Floating-point non-type template parameters
- `[[no_unique_address]]`
- Lambda init-capture with pack expansion
- `explicit(bool)`
- Defaulted `<=>` and `==` with synthesized relational operators
- `__builtin_is_constant_evaluated()` (returns false)
- Constrained `auto` (`Concept auto x = 42`)

### Standard Library
| Header | Parse | Verify | Notes |
|--------|-------|--------|-------|
| `<concepts>` | ✅ | ✅ | |
| `<coroutine>` | ✅ | ✅ | `suspend_never`/`suspend_always` provided as built-ins |
| `<ranges>` | ✅ | ✅ | Some range operations may have no body |
| `<format>` | ✅ | ✅ | |
| `<span>` | ✅ | ✅ | |
| `<bit>` | ✅ | ✅ | |
| `<numbers>` | ✅ | ✅ | |
| `<compare>` | ✅ | ✅ | |
| `<source_location>` | ✅ | ✅ | |
| `<iostream>` | ✅ | ✅ | Works in C++20 mode |
| `<string>`, `<vector>`, `<memory>` | ✅ | ✅ | All work in C++20 mode |

### Known Limitations
- **Coroutine semantics**: `co_return` works for simple cases. `co_await` and `co_yield` are parsed but have no full coroutine state machine lowering.
- **Modules**: Not supported (`import`/`export` not parsed).
- **Concepts in overload resolution**: Concepts are parsed and basic constraint checking works. Complex concept-constrained partial specializations in system headers are handled via error suppression.

---

## C++23

**21 CORE tests, 0 KNOWNBUG.**

### Language Features — working
- Deducing `this` (`void f(this S& self)`)
- `if consteval`
- `auto(x)` decay copy
- Multidimensional `operator[]`
- `static operator()`, `static operator[]`
- `uz`/`UZ` size_t literal suffix
- `#warning`, `#elifdef`/`#elifndef`
- Lambda in unevaluated contexts (`decltype([]{})`)
- Explicit object parameters in lambdas
- `= delete("message")`

### Standard Library
| Header | Status | Notes |
|--------|--------|-------|
| `<expected>` | ✅ parses | |
| `<stacktrace>` | ✅ parses | |
| `<stdfloat>` | ✅ works | |
| `<print>` | ❌ | Not available in g++ 13 |
| `<mdspan>` | ❌ | Not available in g++ 13 |
| `<generator>` | ❌ | Not available in g++ 13 |

---

## C++26

**4 CORE tests, 0 KNOWNBUG.**

### Language Features — working
- Pack indexing `Ts...[N]` in type context
- Pack indexing `ts...[N]` in expression context
- `= delete("message")`
- Function contracts `pre(expr)` / `post(name: expr)` (parsed, stored as annotations)

### Known Gaps
- Reflection (`^`, `[:..:]`) — not started
- Pattern matching — not started
- `constexpr` placement new — not supported

---

## Architecture Notes

### Error Handling for System Headers
System header errors are suppressed at multiple levels to prevent unsupported C++20+ constructs from blocking verification:

1. **Top-level convert loop**: System header items processed with null message handler
2. **Namespace processing**: Same null message handler approach
3. **Method body processing**: Failed system header method bodies cleared to nil
4. **`convert_function`**: System header function bodies cleared on type-check failure
5. **Template member definitions**: Missing class templates silently skipped
6. **Scope resolution fallback**: Global id_map searched when namespace scope not found

### Library Models
- `operator new(size_t)` → delegates to `__new` (CBMC's allocation model)
- `operator delete(void*)` → delegates to `__delete`
- `__normal_iterator::base()` → returns `this->_M_current`
- `std::suspend_never`, `std::suspend_always` → built-in definitions
- `__builtin_coro_*` → stub declarations
- Static variables with `{}` initializer → zero-initialized

### Key Fixes in This Branch
- Member function templates defined out-of-class (`.tcc` files): signature matching prevents overload body swap
- Local RAII structs stripped from template bodies (e.g., `_Guard` in `_M_construct`)
- Constructor calls used as values: `this` pointer correctly added in goto conversion
- Braced-init-list in template arguments: parser handles `Type{args}` in `<...>`
- Shorthand concept constraints: qualified names (`std::integral`) correctly parsed
- Coroutine builtins and trivial awaitables provided as built-ins
