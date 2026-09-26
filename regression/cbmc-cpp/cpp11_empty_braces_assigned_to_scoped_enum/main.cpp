extern "C" void __CPROVER_assert(bool, const char *);
enum class errc
{
  ok = 0,
  bad = 1
};
int main()
{
  errc e = errc::bad;
  e = {};
  __CPROVER_assert(
    e == errc::ok, "assignment of {} value-initializes a scoped enum");
  int i = 5;
  i = {};
  __CPROVER_assert(i == 0, "assignment of {} to an int");
  __CPROVER_assert(e == errc::bad, "WRONG (must FAIL)");
}
