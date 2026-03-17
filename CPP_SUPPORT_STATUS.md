# CBMC C++ Standard Support Status

**Date:** 2026-03-14
**Branch:** `cpp11-parser-rework`
**Compiler:** g++ 13 (libstdc++)

## Summary

| Standard | Headers | Language Features | Overall |
|----------|---------|-------------------|---------|
| C++11    | ★★★★☆  | ★★★★★             | ~95%    |
| C++14    | ★★★★★  | ★★★★★             | ~98%    |
| C++17    | ★★★★☆  | ★★★★☆             | ~90%    |
| C++20    | ★★★★☆  | ★★★☆☆             | ~75%    |
| C++23    | ★★☆☆☆  | ★★★☆☆             | ~40%    |
| C++26    | ★☆☆☆☆  | ★★☆☆☆             | ~20%    |

---

## C++11

**105 regression tests, all passing.**

### Headers (23/24 work)

| Header | Status | Notes |
|--------|--------|-------|
| `<string>` | ✅ Works | `s.size()` verified correctly |
| `<vector>` | ✅ Works | Element access verified; `size()` has pointer arithmetic limitations |
| `<map>` | ✅ Works | Insert and lookup verified |
| `<set>` | ✅ Works | |
| `<list>` | ✅ Works | |
| `<deque>` | ✅ Works | |
| `<array>` | ✅ Works | Size and element access verified |
| `<tuple>` | ✅ Works | `std::get<>` verified |
| `<unordered_map>` | ✅ Works | |
| `<unordered_set>` | ✅ Works | |
| `<memory>` | ✅ Works | `unique_ptr`, `shared_ptr`, `make_shared` all work |
| `<functional>` | ✅ Works | `std::function` verified |
| `<algorithm>` | ✅ Works | |
| `<numeric>` | ✅ Works | |
| `<chrono>` | ✅ Works | |
| `<thread>` | ✅ Works | |
| `<mutex>` | ✅ Works | |
| `<condition_variable>` | ✅ Works | |
| `<future>` | ✅ Works | |
| `<atomic>` | ✅ Works | |
| `<iostream>` | ✅ Works | |
| `<fstream>` | ✅ Works | |
| `<sstream>` | ✅ Works | |
| `<regex>` | ⚠️ Parses | Header parses; `_Scanner` class template body fails silently; regex operations have no body |

### Language Features

| Feature | Status |
|---------|--------|
| `auto` type deduction | ✅ |
| `decltype` | ✅ |
| Range-based `for` | ✅ |
| `nullptr` | ✅ |
| Scoped enums (`enum class`) | ✅ |
| `constexpr` functions | ✅ |
| Lambda expressions | ✅ |
| Rvalue references / move semantics | ✅ |
| `static_assert` | ✅ |
| `alignas` / `alignof` | ✅ |
| Variadic templates | ✅ |
| Template aliases (`using`) | ✅ |
| Delegating constructors | ✅ |
| Inheriting constructors | ✅ |
| User-defined literals | ✅ |
| `noexcept` | ✅ |
| Braced-init-list with `auto` | ✅ (modeled as array) |
| `std::initializer_list<T>` | ⚠️ Partial (modeled as array, no `.size()`) |
| Inline namespaces | ⚠️ Works for unqualified lookup; qualified `std::X` from inline ns requires explicit `std::__ns::X` |

### Known Gaps
- `std::initializer_list<T>` is modeled as a fixed-size array, not the actual class
- `<regex>` operations have no body (the `_Scanner` class template fails during body processing)
- Inline namespace visibility for qualified lookups is incomplete

---

## C++14

**21 regression tests, all passing.**

### Headers
All C++11 headers continue to work. No new C++14-specific headers.

### Language Features

| Feature | Status |
|---------|--------|
| Generic lambdas (`auto` params) | ✅ |
| Return type deduction | ✅ |
| Binary literals (`0b1010`) | ✅ |
| Digit separators (`1'000`) | ✅ |
| Variable templates | ✅ |
| Relaxed `constexpr` | ✅ |
| `[[deprecated]]` attribute | ✅ |
| `std::make_unique` | ✅ |

### Known Gaps
- None significant

---

## C++17

**57 regression tests, all passing.**

### Headers

| Header | Status | Notes |
|--------|--------|-------|
| `<string_view>` | ✅ Works | |
| `<optional>` | ✅ Works | `has_value()` verified |
| `<variant>` | ✅ Works | `std::get<>` verified |
| `<any>` | ✅ Works | |
| `<filesystem>` | ✅ Parses | Header parses; `path` class partially registered (some members fail) |
| `<charconv>` | ✅ Works | |

### Language Features

| Feature | Status |
|---------|--------|
| Structured bindings | ✅ |
| `if` with initializer | ✅ |
| `if constexpr` | ✅ |
| Fold expressions | ✅ |
| Inline variables | ✅ |
| Class template argument deduction (CTAD) | ⚠️ Partial |
| `std::string_view` | ✅ |
| `std::optional` | ✅ |
| `std::variant` | ✅ |
| Nested namespaces (`A::B::C`) | ✅ |
| `[[nodiscard]]`, `[[maybe_unused]]` | ✅ |

### Known Gaps
- `<filesystem>` `path` class has incomplete member registration (constructor resolution for default arguments fails)
- CTAD may not work in all cases

---

## C++20

**64 regression tests, all passing.**

### Headers

| Header | Status | Notes |
|--------|--------|-------|
| `<concepts>` | ✅ Works | |
| `<coroutine>` | ⚠️ Partial | Header parses but `suspend_never`/`suspend_always` not visible via `std::` (inline namespace issue); `co_await`/`co_return` not supported |
| `<ranges>` | ✅ Parses | Header parses; range operations may have no body |
| `<format>` | ✅ Parses | Header parses |
| `<span>` | ✅ Works | |
| `<bit>` | ✅ Works | |
| `<numbers>` | ✅ Works | |
| `<compare>` | ✅ Works | Three-way comparison works |
| `<source_location>` | ✅ Works | |

### Language Features

| Feature | Status |
|---------|--------|
| Concepts (`concept`, `requires`) | ✅ Parsed and type-checked |
| `requires` clauses | ✅ |
| Three-way comparison (`<=>`) | ✅ |
| Designated initializers | ✅ |
| `consteval` | ✅ |
| `constinit` | ✅ |
| Class NTTP with brace init | ✅ (`Fixed{42}` in template args) |
| `co_await` / `co_return` / `co_yield` | ❌ Not supported (parser recognizes keywords but no semantic support) |
| Modules | ❌ Not supported |
| Abbreviated function templates | ✅ |
| `if !consteval` | ✅ |

### Known Gaps
- **Coroutines**: `co_await`, `co_return`, `co_yield` are not semantically supported. The `<coroutine>` header parses but coroutine types (`suspend_never`, `suspend_always`) are not accessible via `std::` due to inline namespace visibility limitations.
- **Modules**: Not supported at all.
- **Concepts**: Parsed and basic type-checking works, but complex concept-constrained overload resolution may fail silently for system headers.
- Many C++20 standard library features have bodies suppressed due to concepts/requires failures in system headers.

---

## C++23

### Headers

| Header | Status | Notes |
|--------|--------|-------|
| `<expected>` | ✅ Parses | |
| `<stacktrace>` | ✅ Parses | |
| `<stdfloat>` | ✅ Works | |
| `<print>` | ❌ Fails | |
| `<mdspan>` | ❌ Fails | |
| `<flat_map>` | ❌ Fails | |
| `<flat_set>` | ❌ Fails | |
| `<generator>` | ❌ Fails | Requires coroutine support |

### Language Features

| Feature | Status |
|---------|--------|
| Deducing `this` | ✅ |
| `if consteval` | ✅ |
| `auto(x)` decay copy | ✅ |
| Multidimensional subscript | ❌ Not tested |
| `static operator()` | ❌ Not tested |
| `std::expected` | ⚠️ Header parses but operations may fail |

### Known Gaps
- Most C++23 library features depend on C++20 concepts which have limited support
- Coroutine-dependent features (`<generator>`) don't work
- `<print>`, `<mdspan>`, `<flat_map>`, `<flat_set>` fail during type-checking

---

## C++26

### Language Features

| Feature | Status |
|---------|--------|
| Pack indexing (`ts...[N]`) | ⚠️ Parsed in type context; expression context (`ts...[0]`) fails to parse |
| `static_assert` with user-generated message | ❌ Not tested |
| Contracts | ❌ Not supported |

### Known Gaps
- C++26 support is minimal
- Pack indexing works for types but not for expressions
- No C++26-specific headers are available in g++ 13

---

## Architecture of Error Handling

A significant portion of the C++17/C++20/C++23 support relies on **graceful error suppression** for system headers:

1. **Top-level convert loop**: System header items are processed with a null message handler, preventing error count increment.
2. **Namespace processing**: Same null message handler approach for namespace items from system headers.
3. **Method body processing**: System header method bodies that fail during `typecheck_code` have their bodies cleared (set to nil) to prevent goto conversion invariant violations.
4. **Template member definitions**: Missing class templates in system headers are silently skipped.
5. **Scope resolution fallback**: When a namespace scope is not found, the global id_map is searched as a fallback.

This means many C++20+ standard library functions will have **no body** during verification. CBMC will treat calls to these functions as havoc (nondeterministic return values). This is sound for verification but means assertions about return values of complex C++20 library functions may fail.

---

## Recommendations for Further Work

### High Impact
1. **C++20 Coroutines**: Implement semantic support for `co_await`, `co_return`, `co_yield`. This would unlock `<generator>` and enable verification of async code.
2. **Inline namespace qualified lookup**: Fix `std::suspend_never` etc. to be findable via `std::` when defined in an inline namespace.
3. **C++20 Concepts in overload resolution**: Currently concepts are parsed but not used for overload resolution. Implementing this would make many more C++20 library functions work correctly.

### Medium Impact
4. **`std::initializer_list<T>`**: Model as the actual class (with `begin()`, `end()`, `size()`) instead of a fixed-size array.
5. **`<filesystem>` path class**: Fix constructor resolution ordering so default arguments can reference constructors declared earlier in the class.
6. **`<regex>` operations**: Fix `_Scanner` class template body processing so regex operations have bodies.

### Lower Impact
7. **C++26 pack indexing in expressions**: Extend parser to handle `ts...[N]` in expression context.
8. **C++23 `<print>`, `<mdspan>`**: These depend on complex C++20 features working correctly.
9. **Modules**: Major infrastructure work; not needed for header-based code.
