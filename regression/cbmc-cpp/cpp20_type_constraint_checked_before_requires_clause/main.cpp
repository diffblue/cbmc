extern "C" void __CPROVER_assert(bool, const char *);

// [temp.constr.decl]/3: the type-constraints come first in the associated
// constraints, and [temp.constr.op]/3: the requires-clause is checked only
// if they are satisfied -- check<int> is never instantiated (its body is
// ill-formed for int); the shape of libstdc++ 16's pair-like constructor
template <class T>
concept pair_like = requires { typename T::first_type; };

template <class T>
struct holder
{
  int which;
  template <class U>
  static constexpr bool check()
  {
    return U::first_type::value;
  }
  template <pair_like U>
    requires(check<U>())
  holder(U) : which(1)
  {
  }
  holder(long) : which(2)
  {
  }
};

int main()
{
  holder<int> h(5);
  __CPROVER_assert(h.which == 2, "type-constraint first");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
