extern "C" void __CPROVER_assert(bool, const char *);
template <typename _Tp>
int probe(__add_rvalue_reference(_Tp) v)
{
  return v + 1;
}
int main()
{
  __CPROVER_assert(probe<int>(41) == 42, "builtin param type");
  return 0;
}
