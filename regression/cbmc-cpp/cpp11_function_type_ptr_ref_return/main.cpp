// N5008 [dcl.decl]/4 + [dcl.ambig.res]: in a declarator, an empty `()`
// following the (possibly pointer/reference-qualified) leading part is a
// function parameter-list, so `int*()`, `int&()`, `int&&()` are function types
// returning `int*` / `int&` / `int&&` -- not just the pointer/reference type
// with the `()` dropped.  A NON-empty parenthesised declarator such as the
// `(*)` in `int(*)()` is a genuine grouping (pointer to function), which must
// be preserved.  g++/clang++ agree.
//
// Regression: CBMC previously parsed `int*()` / `int&()` (empty parens after a
// ptr/ref-operator) as a parenthesised (grouping) declarator and dropped the
// `()`, yielding `int*` / `int&`.  Such a type then failed to match a function
// partial specialization `template <class R, class... A> struct X<R(A...)>`
// (the shape of std::function<R&()>), which is the root of the goto-cc failure
// on util/rename_symbol.cpp via util/expr_iterator.h's
// `std::function<exprt &()>` member.
//
// assertion.6 must FAIL, proving the others are non-vacuous.

template <class T>
struct is_fn
{
  static const int v = 0;
};
template <class R, class... A>
struct is_fn<R(A...)>
{
  static const int v = 1;
};

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  __CPROVER_assert(is_fn<int *()>::v == 1, "int*() is a function type");
  __CPROVER_assert(is_fn<int &()>::v == 1, "int&() is a function type");
  __CPROVER_assert(is_fn<int &&()>::v == 1, "int&&() is a function type");
  __CPROVER_assert(is_fn<int *(char)>::v == 1, "int*(char) is a function type");
  __CPROVER_assert(
    is_fn<int (*)()>::v == 0, "int(*)() is a pointer, not a function");
  __CPROVER_assert(is_fn<int &()>::v == 0, "WRONG must FAIL");
  return 0;
}
