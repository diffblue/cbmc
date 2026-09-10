extern "C" void __CPROVER_assert(bool, const char *);
template <typename _Tp> void probe(__add_rvalue_reference(_Tp));
int main()
{
  bool b = probe<int> && true;
  __CPROVER_assert(b, "function template named, not called");
  return 0;
}
