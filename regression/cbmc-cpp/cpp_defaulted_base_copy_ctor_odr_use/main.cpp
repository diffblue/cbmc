// An explicitly-defaulted base-class copy constructor must be elaborated when
// it is odr-used by a derived class's (implicitly-defined) copy constructor.
//
// The derived class's implicitly-defined copy constructor copies its base
// subobject ([class.copy.ctor]/14) by invoking the base copy constructor.  For
// a class-template instance whose members are lazily instantiated, that base
// copy constructor is an explicitly-defaulted special member whose body is
// produced on demand.  Its odr-use appears only as a class-name constructor
// call in the synthesized body (resolved to the concrete overload during goto
// conversion), so it was missed by the lazy-instantiation reference scan and
// reached goto-symex without a body ([temp.inst]/4 requires it to be
// instantiated).

extern "C" int __VERIFIER_nondet_int();
extern "C" void __CPROVER_assert(int, const char *);

template <typename...>
struct tuple;

template <unsigned long _Idx, typename _Head>
struct _Tuple_impl
{
  _Head h;
  _Tuple_impl() = default;
  _Tuple_impl(const _Tuple_impl &) = default;
  _Tuple_impl(_Head x) : h(x)
  {
  }
  template <typename _UHead>
  _Tuple_impl(_UHead &&u) : h(u)
  {
  }
};

template <typename _T1, typename _T2>
struct tuple<_T1, _T2> : _Tuple_impl<0, _T1>
{
  tuple() = default;
  tuple(_T1 x) : _Tuple_impl<0, _T1>(x)
  {
  }
};

int main()
{
  int v = __VERIFIER_nondet_int();
  tuple<int, int> a(v);
  tuple<int, int> b = a; // copies the _Tuple_impl base via its defaulted copy ctor
  __CPROVER_assert(b.h == v, "defaulted base copy constructor preserves value");
  return 0;
}
