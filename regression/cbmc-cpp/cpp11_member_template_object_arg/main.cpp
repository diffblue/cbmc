// N5008 [over.match.funcs]/2: in overload resolution for a member function,
// the implicit object argument pairs with the implicit object parameter.
// The argument-vs-parameter convertibility pre-filter used during function
// template argument deduction must skip BOTH together.
//
// Was KNOWNBUG: the filter skipped the `this` parameter but not the object
// operand, pairing the object against the first REAL parameter.  For a
// member template like `construct(_Up*, pc_t, tuple<int&&>)` the object was
// compared against `pc_t` and the candidate wrongly rejected as
// not-convertible, so the call found no match and the enclosing body was
// dropped (the allocator_traits::construct -> __a.construct chain behind
// std::map's node construction).
extern "C" void __CPROVER_assert(int, const char *);

struct pc_t
{
};
template <typename... E>
struct tuple
{
};
template <>
struct tuple<int &&>
{
  int v;
  tuple(int &&x) : v(x)
  {
  }
};

template <typename T1, typename T2>
struct pair
{
  T1 first;
  T2 second;
  pair() : first(), second()
  {
  }
  template <typename U>
  pair(pc_t, U t1) : first(t1.v), second(7)
  {
  }
};

struct maker
{
  template <typename _Up>
  int construct(_Up *, pc_t, tuple<int &&> t1)
  {
    _Up tmp(pc_t{}, t1);
    return tmp.first * 10 + tmp.second;
  }
};

int main()
{
  int x = 4;
  tuple<int &&> t1(static_cast<int &&>(x));
  maker m;
  pair<const int, int> *dummy = 0;
  __CPROVER_assert(
    m.construct(dummy, pc_t{}, t1) == 47, "member template deduction");
  return 0;
}
