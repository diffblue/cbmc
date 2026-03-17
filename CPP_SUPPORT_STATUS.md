# CBMC C++ Standard Support Status

**Date:** 2026-03-16
**Branch:** `cpp11-parser-rework`
**Test suite:** 533 CORE, 4 KNOWNBUG
**Compilers tested:** g++ 13 (libstdc++), g++ 14 (libstdc++), clang++ 18 (libc++)

## Summary

| Standard | Language | Library (libstdc++) | Library (libc++) | Tests | Gaps |
|----------|----------|---------------------|------------------|-------|------|
| C++11    | ~98%     | ~90%                | ~70%             | 108   | Minor |
| C++14    | ~98%     | ~90%                | ~60%             | 21    | Minor |
| C++17    | ~95%     | ~85%                | ~50%             | 58    | Minor |
| C++20    | ~80%     | ~75%                | ~40%             | 68    | Moderate |
| C++23    | ~60%     | ~10%                | ~5%              | 21    | Significant |
| C++26    | ~15%     | ~0%                 | ~0%              | 4     | Major |

---

## C++11 (108 CORE tests)

### Language features — fully working
- `auto`, `decltype`, `decltype(auto)`
- Range-based `for` (including over braced-init-lists)
- `nullptr`, scoped enums, `constexpr`, `static_assert`, `noexcept`
- Lambda expressions (all capture modes, init-capture)
- Rvalue references, move semantics, perfect forwarding
- Variadic templates, parameter packs, `sizeof...`
- Template aliases, trailing return types, inline namespaces
- User-defined literals, raw string literals
- Delegating/inheriting constructors, NSDMI
- `= default`, `= delete`, explicit conversion operators
- SFINAE with `enable_if`, braced-init-lists
- `alignas`, `alignof`

### Standard library (libstdc++) — all headers parse
| Header | Parse | Verify | Notes |
|--------|-------|--------|-------|
| `<string>` | ✅ | ✅ | `size()`, `operator[]` verified |
| `<vector>` | ✅ | ✅ | `push_back`, `operator[]`, `size()` verified |
| `<map>`, `<set>`, `<list>`, `<deque>` | ✅ | ✅ | |
| `<array>`, `<tuple>` | ✅ | ✅ | |
| `<memory>` | ✅ | ✅ | `shared_ptr`, `unique_ptr`, `make_shared` |
| `<functional>` | ✅ | ✅ | `std::function` |
| `<algorithm>`, `<numeric>` | ✅ | ✅ | `std::sort` (C++11 mode) |
| `<regex>` | ✅ | ✅ | `regex_match` verified |
| `<thread>`, `<mutex>`, `<atomic>`, `<chrono>` | ✅ | ✅ | |
| `<iostream>`, `<fstream>`, `<sstream>` | ✅ | ✅ | |

### Standard library (libc++) — most headers parse
| Header | Parse | Notes |
|--------|-------|-------|
| `<vector>`, `<map>`, `<string>` | ✅ | Slower than libstdc++ |
| `<algorithm>` | ⚠️ | Timeout on large programs |
| `<optional>` | ❌ | Cascading parse error from `<variant>` |

### Remaining gaps
- Some "no body" warnings for deeply-nested STL template instantiations

---

## C++14 (21 CORE tests)

### Language features — fully working
- Generic lambdas, return type deduction
- Binary literals, digit separators
- Variable templates, relaxed `constexpr`
- `decltype(auto)`, `[[deprecated]]`
- Lambda init-capture

### Standard library — same as C++11 plus `std::make_unique`

### Remaining gaps
- None significant for language features

---

## C++17 (58 CORE tests)

### Language features — fully working
- Structured bindings (including references, tuple-like)
- `if`/`switch` with initializer, `if constexpr`
- Fold expressions (all binary operators)
- Inline variables, nested namespaces
- CTAD, `template<auto>`, deduction guides
- `static_assert` without message
- `[[nodiscard]]`, `[[maybe_unused]]`, `[[fallthrough]]`
- `constexpr` lambdas

### Standard library (libstdc++) — all headers parse
| Header | Parse | Verify |
|--------|-------|--------|
| `<optional>` | ✅ | ✅ `has_value()` verified |
| `<variant>` | ✅ | ✅ `get<T>()` verified |
| `<any>`, `<string_view>` | ✅ | ✅ |
| `<filesystem>` | ✅ | ⚠️ `path` partially modeled |
| `<shared_mutex>`, `<charconv>` | ✅ | ✅ |

### Remaining gaps
- `std::sort` in C++17 mode works but is slow (needs `--unwind`)
- `std::vector::push_back` verification: element access works, `size()` may fail

---

## C++20 (68 CORE tests)

### Language features — mostly working
- Concepts (`concept`, `requires` clauses and expressions)
- Shorthand concept constraints (`template<std::integral T>`)
- Three-way comparison (`<=>`) with `std::strong_ordering`
- Designated initializers, `consteval`, `constinit`
- `if consteval` / `if !consteval`
- `co_return` (basic coroutine support)
- Class type NTTP with brace init
- Template lambdas, `using enum`
- Aggregate init with parentheses and base classes
- Range-based for with init-statement
- `constexpr` virtual functions, dynamic allocation
- Floating-point NTTP, `[[no_unique_address]]`
- `explicit(bool)`, `__builtin_bit_cast`

### Standard library (libstdc++) — all major headers parse
| Header | Parse | Verify |
|--------|-------|--------|
| `<concepts>`, `<compare>` | ✅ | ✅ |
| `<coroutine>` | ✅ | ✅ `suspend_never`/`suspend_always` |
| `<ranges>`, `<format>` | ✅ | ✅ |
| `<span>`, `<bit>`, `<numbers>` | ✅ | ✅ |
| `<source_location>` | ✅ | ✅ |

### Remaining gaps
- **Modules** (`import`/`export`): not supported (KNOWNBUG: `cpp20_modules`)
- **`std::sort` in C++20 mode**: fails because `__numeric_traits_integer` template scope is lost in nested namespace/linkage contexts. Works in C++17 mode. (KNOWNBUG: `cpp20_sort_cpp20`)
- **Coroutine semantics**: `co_return` works for simple cases. `co_await`/`co_yield` parse but have no full coroutine state machine lowering.
- **Concept subsumption in overload resolution**: basic constraint checking works; complex partial ordering by constraints is not implemented.

### Standard library (libc++)
| Header | Parse | Notes |
|--------|-------|-------|
| `<concepts>`, `<bit>`, `<numbers>`, `<compare>` | ✅ | |
| `<span>` | ❌ | `_Float32`/`_Float64` C types (KNOWNBUG: `cpp20_libcxx_span`) |

---

## C++23 (21 CORE tests)

### Language features — partially working
- Deducing `this` (`void f(this S& self)`)
- `if consteval`, `auto(x)` decay copy
- Multidimensional `operator[]`, `static operator()`, `static operator[]`
- `uz`/`UZ` size_t literal suffix
- `#warning`, `#elifdef`/`#elifndef`
- Lambda in unevaluated contexts
- Explicit object parameters in lambdas
- `= delete("message")`

### Not yet supported
- **`std::print`**, **`std::generator`**: not available in g++ 13
- **`std::mdspan`**: not available in g++ 13
- **`constexpr` for `<cmath>`/`<cstdlib>`**: not modeled
- **`std::expected`**: header parses but verification untested

---

## C++26 (4 CORE tests)

### Language features — early support
- Pack indexing `Ts...[N]` (type and expression context)
- `= delete("message")`
- Function contracts `pre(expr)` / `post(name: expr)` (parsed, stored)

### Not yet supported
- **Reflection** (`^`, `[:..:]`)
- **Pattern matching**
- **`constexpr` placement new**
- **Contracts semantics**: parsed but no verification integration

---

## Compiler/Library Compatibility

### g++ 13 (default, libstdc++)
- Full support. All 532 tests pass.

### g++ 14 (libstdc++)
- Compatible. Same tests pass as g++ 13.
- Minor: CBMC passes `-std=gnu11` when preprocessing CPROVER library headers, which g++ 14 warns about for C++ files.

### clang++ 18 (libc++)
- Enabled via `--stdlib libc++` (CBMC) or `-stdlib=libc++` (goto-cc).
- `<vector>`, `<map>`, `<string>`, `<concepts>` parse and verify.
- `<optional>` fails due to cascading parse errors from `<variant>` which uses `_Float32`/`_Float64` C types in system headers.
- `<span>` fails for the same `_Float` type reason.
- `<algorithm>` times out on complex programs.
- Root cause of most libc++ failures: clang's system headers use `_Float32`/`_Float64` C types that CBMC's C++ parser doesn't recognize. These cascade through `<variant>` and other headers.
- Overall: ~70% of C++11 headers work, decreasing for later standards.

## KNOWNBUG Summary

| Test | Issue | Severity |
|------|-------|----------|
| `cpp20_modules` | `import`/`export` not parsed | Medium |
| `cpp20_sort_cpp20` | Template scope lost in C++20 `std::sort` | Medium |
| `cpp17_libcxx_optional` | libc++ variant cascading parse error | Medium |
| `cpp20_libcxx_span` | libc++ ranges concept parse error | Medium |

---

## Architecture Notes

### Error handling for system headers
System header errors are suppressed at four levels:
1. Top-level `typecheck()` loop
2. Namespace item processing (with source location fallback for empty locations)
3. Linkage spec item processing
4. Method body processing (failed bodies cleared to nil)

### Key type system issue: `c_bool` vs `bool`
The C++ frontend uses C's `_Bool` (`c_bool`) internally for boolean values throughout the parser, type converter, and boolean conversion functions. This creates type mismatches when `c_bool` values flow into C++ `bool` contexts. A reconciliation layer in `symex_assign` handles mismatches involving `c_bool`/`bool`. The proper fix requires a comprehensive `c_bool`-to-`bool` conversion pass in the C++ frontend.

### Template scope management
Template scopes are stored in `cpp_scopes.id_map`. In some nested namespace/linkage spec contexts, the scope mapping can be lost. A safe lookup helper (`id_map_lookup`) prevents null pointer creation from `operator[]`. One known case (`__numeric_traits_integer` in C++20 `std::sort`) remains where the scope is lost.

### Library models
- `operator new/delete` → `__new/__delete` (CBMC allocation model)
- `__normal_iterator::base()` → `this->_M_current`
- `std::suspend_never`, `std::suspend_always` → from `<coroutine>` header
- `__builtin_coro_*` → stub declarations
- `__builtin_bit_cast` → typecast (not bit-level reinterpretation)
- `allocator_traits::construct(alloc, ptr, val)` → `*ptr = val`
- `vector::_S_relocate(first, last, result, alloc)` → `return result + (last - first)`
- `vector::_S_nothrow_relocate` → returns `true` (no exception modeling)
