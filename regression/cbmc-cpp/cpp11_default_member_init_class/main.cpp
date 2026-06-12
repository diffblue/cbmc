// A defaulted default constructor must value-initialize a class-typed member
// that has an empty brace default member initializer `m{}`
// (N5008 [class.base.init], [dcl.init]).  Previously the empty `{}` was
// type-checked into an uninitialized temporary that was copied into the
// member, leaving it indeterminate.  This is the shape of libstdc++'s
// _Hashtable_ebo_helper<_Nm, _Tp, false>, which holds `_Tp _M_tp{};`.

struct inner
{
  int x;
};

struct plain
{
  plain() = default;
  inner m{};
};

// Partial-specialized class template member holding `T m{}` (the EBO shape).
template <int N, class T, bool Ebo>
struct helper;

template <int N, class T>
struct helper<N, T, false>
{
  helper() = default;
  T m{};
};

int main()
{
  plain p;
  __CPROVER_assert(p.m.x == 0, "plain member value-initialized");

  helper<0, inner, false> h;
  __CPROVER_assert(h.m.x == 0, "partial-spec member value-initialized");

  return 0;
}
