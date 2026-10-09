extern "C" void __CPROVER_assert(bool, const char *);
struct factoryt
{
  template <class _Np>
  auto make(_Np)
  {
    return _Np(21) + _Np(21);
  }
};
int main()
{
  factoryt f;
  __CPROVER_assert(f.make(0) == 42, "eager auto-return under instance map");
  return 0;
}
