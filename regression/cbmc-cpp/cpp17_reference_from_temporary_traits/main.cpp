extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  constexpr bool b = __reference_converts_from_temporary(const int &, int);
  __CPROVER_assert(b, "int binds const int& via temporary");
  constexpr bool c = __reference_converts_from_temporary(int &, int);
  __CPROVER_assert(!c, "no lvalue-ref binding from temporary");
  return 0;
}
