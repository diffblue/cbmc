// Real translation unit: CBMC's own src/goto-programs/
// restrict_function_pointers.cpp (named on the options line).  See
// test.desc: std::__shared_count's constructor template must not be
// instantiated for std::nullptr_t.
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  int reached = 1;
  __CPROVER_assert(reached == 1, "the translation unit converts");
  __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
  return 0;
}
