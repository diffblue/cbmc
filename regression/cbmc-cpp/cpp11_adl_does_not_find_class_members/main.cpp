// N5008 [basic.lookup.argdep]/4: argument-dependent lookup finds functions
// in the associated namespaces and friends of the associated classes, not
// the classes' members.  For `value(step, 1)' with an argument of type
// step_t, ADL searched step_t's scope and found the data member
// step_t::value: "symbol 'value' does not uniquely resolve" (CBMC's own
// xml_goto_trace.cpp: the function full_lhs_value and the member
// goto_trace_stept::full_lhs_value, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct step_t
{
  enum class typet
  {
    A,
    B
  };
  typet type = typet::B;
  int value = 5;
};
int value(const step_t &s, int k)
{
  return s.value + k;
}
int convert(const step_t &step)
{
  switch(step.type)
  {
  case step_t::typet::A:
  case step_t::typet::B:
  {
    // N5008 [basic.lookup.unqual]: `value' is the namespace-scope function;
    // the member step_t::value is not in scope here
    return value(step, 1);
  }
  }
  return 0;
}
int main()
{
  step_t s;
  __CPROVER_assert(convert(s) == 6, "free function found");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
