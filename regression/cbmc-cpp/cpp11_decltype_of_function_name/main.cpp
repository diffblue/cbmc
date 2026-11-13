extern "C" void __CPROVER_assert(bool, const char *);
int add(int a, int b)
{
  return a + b;
}
template <class T>
struct is_pointer
{
  static const bool value = false;
};
template <class T>
struct is_pointer<T *>
{
  static const bool value = true;
};
// [dcl.type.decltype]/1.3: decltype(add) is the type of the entity, the
// function type int(int, int) -- no function-to-pointer conversion
int main()
{
  decltype(add) *p = add;
  __CPROVER_assert(!is_pointer<decltype(add)>::value, "not a pointer type");
  __CPROVER_assert(is_pointer<decltype(&add)>::value, "address is a pointer");
  __CPROVER_assert(p(1, 2) == 3, "pointer to it");
  __CPROVER_assert(p(1, 2) != 3, "WRONG (must FAIL)");
}
