// N5008 [over.call]: a static operator().
extern "C" void __CPROVER_assert(bool, const char *);
struct F
{
  static int operator()(int x)
  {
    return x + 1;
  }
};
int main()
{
  __CPROVER_assert(F{}(1) == 2, "static operator()");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
