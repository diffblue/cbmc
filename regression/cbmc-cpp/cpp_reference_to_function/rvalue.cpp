extern "C" void __CPROVER_assert(bool, const char *);
int hit;
void cb(int k)
{
  hit = k;
}
// [dcl.init.ref]/5.3.1: an rvalue reference to function binds to the
// function lvalue; a function alias (libc++'s __callback_fn_t) works the same
using F = void(int);
int main()
{
  void (&&r)(int) = cb;
  r(1);
  __CPROVER_assert(hit == 1, "rvalue reference");
  F &a = cb;
  a(2);
  __CPROVER_assert(hit == 2, "reference through alias");
  __CPROVER_assert(hit != 2, "WRONG (must FAIL)");
}
