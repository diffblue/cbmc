extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int v;
};
template <class H>
struct leaf
{
  template <class T>
  static constexpr bool can_bind_reference()
  {
    return !__reference_binds_to_temporary(H, T);
  }
};
int main()
{
  __CPROVER_assert(
    leaf<const int &>::can_bind_reference<int &>(),
    "int& binds to const int& without a temporary");
  __CPROVER_assert(
    !leaf<const int &>::can_bind_reference<long>(),
    "long binds to const int& only through a temporary");
  __CPROVER_assert(
    leaf<const S &>::can_bind_reference<S>(), "same-type class binding");
  __CPROVER_assert(
    leaf<const int &>::can_bind_reference<long>(), "WRONG (must FAIL)");
}
