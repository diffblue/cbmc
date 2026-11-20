// The MSVC runtime's exception data (vcruntime_exception.h):
// __std_exception_copy is defined in the runtime.  N5008 [exception]/2:
// an exception and its copy have equal what() strings, also for a copy of
// a copy.
extern "C" void __CPROVER_assert(bool, const char *);
extern "C"
{
  struct __std_exception_data
  {
    const char *_What;
    bool _DoFree;
  };
  void __cdecl __std_exception_copy(
    const __std_exception_data *_From,
    __std_exception_data *_To);
  void __cdecl __std_exception_destroy(__std_exception_data *_Data);
  void *malloc(decltype(sizeof 0));
  void free(void *);
}

int main()
{
  __std_exception_data a = {"bad locale name", true};
  __std_exception_data b, c;
  __std_exception_copy(&a, &b);
  __std_exception_copy(&b, &c);
  __CPROVER_assert(
    c._What != nullptr && c._What[0] == 'b' && c._What[14] == 'e' &&
      c._What[15] == 0 && c._DoFree,
    "the copy of a copy has the same message");
  __std_exception_destroy(&b);
  __std_exception_destroy(&c);
  __CPROVER_assert(c._What == nullptr, "destroyed");
  __CPROVER_assert(c._What != nullptr, "WRONG (must FAIL)");
  return 0;
}
