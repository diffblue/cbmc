extern "C" void __CPROVER_assert(bool, const char *);
enum E
{
  e0,
  e1,
  e2
};
template <class T, unsigned long N>
struct arr
{
  T v[N];
};
template <class T>
constexpr E to_e()
{
  return e2;
}
struct IA
{
  int v[2];
  int w;
};
struct P
{
  int x;
};
struct N
{
  P p;
  int y;
};
// [stmt.return]/2, [dcl.init.list]/3.4, [dcl.init.aggr]/16: a
// braced-init-list operand aggregate-initializes the result object, with
// brace elision for the array and class members
IA g()
{
  return {1, 2, 3};
}
N n()
{
  return {4, 5};
}
// libstdc++'s basic_format_args::_S_types_to_pack into std::array
template <class... A>
arr<E, sizeof...(A)> pack()
{
  return {to_e<A>()...};
}
// [over.ics.list]/8: the list converts to the aggregate parameter
int h(IA a)
{
  return a.v[1] + a.w;
}
// [dcl.init.list]/3.2: a single element of the class type initializes the
// object from it
P q(P x)
{
  return {x};
}
int main()
{
  __CPROVER_assert(g().v[1] == 2 && g().w == 3, "return");
  __CPROVER_assert(n().p.x == 4 && n().y == 5, "nested class member");
  __CPROVER_assert(pack<int, char>().v[1] == e2, "pack expansion");
  __CPROVER_assert(h({1, 2, 3}) == 5, "argument");
  P p{7};
  __CPROVER_assert(q(p).x == 7, "same class");
  __CPROVER_assert(g().w != 3, "WRONG (must FAIL)");
}
