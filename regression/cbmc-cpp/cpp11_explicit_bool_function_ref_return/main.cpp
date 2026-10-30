// N5008 [dcl.decl]/4 + [conv.bool]: `std::function<exprt &()>` (a function
// object wrapping a nullary function returning a reference) has an explicit
// operator bool, contextually converted in `if(f)`.  This mirrors
// util/expr_iterator.h's `std::function<exprt &()> mutate_root; ... if
// (mutate_root)`, the shape behind the goto-cc failure on rename_symbol.cpp.
//
// Here `fn<int &()>` matches the function-type partial specialization (return
// type `int&`, no parameters) and provides an explicit operator bool.  Because
// the empty `()` after the reference return type is now parsed as a function
// parameter-list (not dropped), the specialization matches and the boolean
// conversion resolves.  g++/clang++ agree that m() returns 0 when the wrapped
// object is invalid.
//
// assertion.2 must FAIL, proving assertion.1 is non-vacuous.

template <class>
struct fn;
template <class R, class... A>
struct fn<R(A...)>
{
  bool valid;
  explicit operator bool() const
  {
    return valid;
  }
};

struct holder
{
  fn<int &()> callback;
  int use() const
  {
    if(callback)
      return 1;
    return 0;
  }
};

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  holder h;
  h.callback.valid = false;
  __CPROVER_assert(
    h.use() == 0, "explicit operator bool of fn<int&()> in boolean context");
  __CPROVER_assert(h.use() != 0, "WRONG must FAIL");
  return 0;
}
