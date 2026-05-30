// Regression for two related fixes in CBMC's C++ frontend:
//
// 1. The constexpr `_S_use_relocate` body override in
//    `cpp_typecheck.cpp` now wraps the constant in a
//    `code_block { return; }` rather than assigning a bare
//    `true_exprt()` to the symbol's `value`.  Without the wrap,
//    `convert_function`'s precondition that
//    `symbol.value.id() == ID_code` rejects the symbol with
//      function 'std::vector<...>::_S_use_relocate()' is initialized
//      with constant
//    when `typecheck_method_bodies` reaches it (after the override).
//
// 2. `typecheck_expr_explicit_constructor_call` previously
//    unconditionally expanded a brace-init-list `{e1, ..., en}`
//    operand into `[e1, ..., en]` and called `new_temporary` with
//    those as args.  This skipped phase 2.1 of [over.match.list]/2:
//    when T has an `initializer_list<U>` constructor, the
//    brace-init-list should be passed AS A WHOLE (single argument
//    of type `initializer_list<U>`).  The unconditional expansion
//    meant
//      std::vector<X>{x1, x2}
//    never matched `vector(initializer_list<X>, alloc&)` and failed
//    with
//      found no match for symbol 'vector', candidates are: ...
//      argument types: <X>
//    when no `vector(X, X, ...)` ctor existed.  The fix preserves
//    the brace-init-list as a single operand when T has a non-
//    explicit `initializer_list<U>` constructor whose extra
//    parameters all have default values.

#include <utility>
#include <vector>

struct symbol_exprt
{
  int x;
  symbol_exprt() : x(0)
  {
  }
};

void take_vec(std::vector<symbol_exprt>)
{
}

int main()
{
  symbol_exprt s;

  // The functional-cast brace-init form `T{x}` of a non-POD class
  // type with an `initializer_list<X>` ctor (here, `vector`).
  // Before the fix this matched no `vector` ctor and reported
  // "found no match for symbol 'vector'".  With the fix, phase 2.1
  // of [over.match.list]/2 picks the `initializer_list<X>` ctor.
  take_vec(std::vector<symbol_exprt>{std::move(s)});

  // Vector declarations with brace-init: this path was already
  // working before the fix but exercises the same code path.
  std::vector<symbol_exprt> v1{symbol_exprt()};

  // Brace-init with multiple elements of the value_type.
  symbol_exprt s2, s3;
  std::vector<symbol_exprt> v2{symbol_exprt(), std::move(s2), std::move(s3)};

  return 0;
}
