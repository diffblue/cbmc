// N5008 [dcl.fct]: a member function with an explicit object parameter.
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int v = 3;
  template <class Self>
  int get(this Self &&s)
  {
    return s.v;
  }
};
int main()
{
  S s;
  __CPROVER_assert(s.get() == 3, "explicit object parameter");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
