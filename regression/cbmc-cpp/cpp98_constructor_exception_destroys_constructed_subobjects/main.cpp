// N5008 [except.ctor]/3: if the initialization of a subobject is terminated
// by an exception, the destructors of the subobjects already initialized
// are invoked, in reverse order of construction
extern "C" void __CPROVER_assert(bool, const char *);
int log_[8];
int n = 0;
struct M
{
  int id;
  M(int i) : id(i)
  {
    log_[n++] = i;
  }
  ~M()
  {
    log_[n++] = -id;
  }
};
struct Thrower
{
  Thrower()
  {
    throw 42;
  }
};
struct B
{
  M b;
  B() : b(1)
  {
  }
};
struct S : B
{
  M m2;
  Thrower t;
  M m3;
  S() : m2(2), m3(3)
  {
  }
};
int main()
{
  try
  {
    S s;
  }
  catch(int)
  {
    log_[n++] = 100;
  }
  __CPROVER_assert(
    n == 5 && log_[0] == 1 && log_[1] == 2 && log_[2] == -2 && log_[3] == -1 &&
      log_[4] == 100,
    "unwound in reverse");
  __CPROVER_assert(n == 3, "WRONG (must FAIL)");
}
