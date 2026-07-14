// N5008 [temp.inst]/2, [temp.deduct]/5: a constructor template of a class
// template instance, constrained by a SFINAE default template argument whose
// constexpr callee is a member function template of ANOTHER class template
// (instantiated over the class's pack) and whose body uses the callee's OWN
// parameter pack (sizeof...(Us)), is instantiable when the enclosing class
// instance is constructed from a function template.  This is the shape of
// libstdc++ std::tuple's constrained constructors called from
// std::make_tuple.
//
// Fixed per [temp.deduct]/5: the values of deduced template parameters are
// available when subsequent default template arguments are instantiated --
// the deduced ELEMENT TYPES of the constructor template's parameter pack are
// now recorded (not only its size) before default template arguments are
// evaluated, so the `Us...` expansion in the constraint no longer collapses
// to an empty argument list and the constexpr guard folds over the real
// arguments.  Each ingredient of this shape was verified necessary by
// single-dimension toggling; g++ and clang++ accept and run this test.

extern "C" void __CPROVER_assert(int, const char *);

template<bool, typename T = void>
struct enable_if
{
};
template<typename T>
struct enable_if<true, T>
{
  typedef T type;
};
template<bool B, typename T = void>
using enable_if_t = typename enable_if<B, T>::type;

template<typename... Ts>
struct TCs
{
  template<typename... Us>
  static constexpr bool ok()
  {
    return sizeof...(Us) == sizeof...(Ts);
  }
};

template<typename... Es>
struct tup
{
  int first;
  template<typename... Us,
           enable_if_t<TCs<Es...>::template ok<Us...>(), bool> = true>
  tup(Us &&... u) : first(pick(u...))
  {
  }
  template<typename U0, typename... R>
  static int pick(U0 &&u0, R &&...)
  {
    return (int)u0;
  }
};

template<typename... Es>
tup<Es...> mk(Es... e)
{
  return tup<Es...>(e...);
}

int main()
{
  auto t1 = mk(5);
  __CPROVER_assert(t1.first == 5, "arity 1");
  auto t3 = mk(7, 6.0, 'a');
  __CPROVER_assert(t3.first == 7, "arity 3");
  return 0;
}
