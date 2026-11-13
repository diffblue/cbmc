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

// A class whose own default member initializer is a scalar `{}` (the value
// must be zero, not an indeterminate/ill-typed value).
struct scalar_nsdmi
{
  int n{};
};

// A member with NO default member initializer whose TYPE has one: the
// enclosing defaulted constructor must still default-construct it so the
// member type's NSDMI takes effect ([class.base.init], [class.default.ctor]/3
// — an NSDMI makes the default constructor non-trivial).
struct holds_nsdmi_member
{
  holds_nsdmi_member() = default;
  scalar_nsdmi s; // no initializer here; scalar_nsdmi::n{} must still apply
};

int main()
{
  plain p;
  __CPROVER_assert(p.m.x == 0, "plain member value-initialized");

  helper<0, inner, false> h;
  __CPROVER_assert(h.m.x == 0, "partial-spec member value-initialized");

  scalar_nsdmi s;
  __CPROVER_assert(s.n == 0, "scalar NSDMI value-initialized");

  holds_nsdmi_member hn;
  __CPROVER_assert(hn.s.n == 0, "member-type NSDMI applied via default ctor");

  return 0;
}
