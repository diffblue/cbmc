extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct is_member_fn
{
  static constexpr int arity = -1;
};
// N5008 [temp.deduct.type]/8: `R (C::*)(A...)' and `R (C::*)(A) const'
// deduce R, C and the parameter types A from a pointer to member function
// type (the MSVC STL's _Is_memfunptr, behind std::invoke and std::bind)
template <class R, class C, class... A>
struct is_member_fn<R (C::*)(A...)>
{
  static constexpr int arity = sizeof...(A);
};
template <class R, class C, class A>
struct is_member_fn<R (C::*)(A) const>
{
  static constexpr int arity = 1;
};
struct S
{
  int k;
  int mul(int a) const
  {
    return k * a;
  }
  int add(int a, int b)
  {
    return k + a + b;
  }
};
template <class R, class C, class A>
constexpr int take(R (C::*)(A) const)
{
  return 1;
}
constexpr int take(...)
{
  return 2;
}
int main()
{
  __CPROVER_assert(
    is_member_fn<decltype(&S::mul)>::arity == 1 &&
      is_member_fn<decltype(&S::add)>::arity == 2 &&
      is_member_fn<int>::arity == -1 && take(&S::mul) == 1,
    "parameter types deduced");
  __CPROVER_assert(take(&S::mul) == 2, "WRONG (must FAIL)");
  return 0;
}
