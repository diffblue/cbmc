// N5008 [temp.constr.atomic]/3: substitution failure (and an
// unsatisfied constraint) removes the candidate.  The clause calls a
// consteval static member (`ok<U>()`, the libstdc++ C++20 pair
// _S_constructible shape) whose evaluation initially THREW inside the
// front end (callee body not yet prepared) -- the candidate was then
// kept, beating the viable const-ref constructor, and the int literal
// 0 was forwarded into the pointer member.
//
// Fixed by retrying the tri-state evaluation on the substituted
// clause after a whole-clause type-check failure; the call-atom fold
// prepares the deferred callee body and decides the constraint.
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
  template <class U>
  static constexpr bool ok()
  {
    return is_constructible<T, U>::value;
  }
  constexpr prt(const T &b) : second(b)
  {
  }
  template <class U = T>
    requires(ok<U>())
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
