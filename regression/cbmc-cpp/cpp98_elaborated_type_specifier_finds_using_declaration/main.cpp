// N5008 [basic.lookup.elab]/1, [namespace.udecl]/1: `struct timespec'
// looks up the name; a using-declaration (<ctime>'s `namespace std { using
// ::timespec; }') makes it find the global class, so no new class is
// declared
extern "C" void __CPROVER_assert(bool, const char *);
struct timespec
{
  long tv_sec;
  long tv_nsec;
};
namespace n
{
using ::timespec;
long elaborated(long s)
{
  struct timespec ts = {s, 3};
  return ts.tv_sec + ts.tv_nsec;
}
struct semaphore
{
  long member(long s)
  {
    struct timespec ts = {s, 2};
    return ts.tv_sec + ts.tv_nsec;
  }
};
} // namespace n
int main()
{
  __CPROVER_assert(n::elaborated(1) == 4, "namespace function");
  n::semaphore x;
  __CPROVER_assert(x.member(1) == 3, "member function");
  struct timespec *p = 0;
  __CPROVER_assert(p == 0, "global scope");
  __CPROVER_assert(x.member(1) == 4, "WRONG (must FAIL)");
}
