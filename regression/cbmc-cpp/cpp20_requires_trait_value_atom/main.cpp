// N5008 [temp.constr.atomic]/1,3: the atomic constraint
// is_constructible<T, U>::value is contextually converted to bool; for
// T = nodet*, U = int it is FALSE, so the forwarding constructor must
// drop out of overload resolution and the const-ref constructor (with
// the literal 0 converting to a null pointer, [conv.ptr]/1) must win.
//
// This used to fail: the folded trait member is a c_bool constant,
// which the satisfaction evaluator's is_true/is_false did not
// recognize -- the definitively FALSE clause stayed "unknown", the
// unsatisfiable forwarding constructor was kept and won, and the int
// literal was forwarded into the pointer member (the shape behind
// std::map's corrupted _M_get_insert_*_pos results).
//
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);
struct nodet
{
  int v;
};
template <bool v>
struct bool_constant
{
  static constexpr bool value = v;
};
template <class T, class U>
struct is_constructible : bool_constant<__is_constructible(T, U)>
{
};
template <class T>
struct prt
{
  T second;
  constexpr prt(const T &b) : second(b)
  {
  }
  template <class U = T>
    requires(is_constructible<T, U>::value)
  constexpr prt(U &&b) : second(static_cast<U &&>(b))
  {
  }
  ~prt()
  {
  }
};
nodet g;
prt<nodet *> make()
{
  return prt<nodet *>(0); // int argument: forwarding ctor must SFINAE out
}
int main()
{
  prt<nodet *> r = make();
  __CPROVER_assert(r.second == nullptr, "second is null");
  return 0;
}
