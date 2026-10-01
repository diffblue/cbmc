extern "C" void __CPROVER_assert(bool, const char *);
int hit;
void cb(int k)
{
  hit = k;
}
// [dcl.init.ref]/5.1.1: the function lvalue cb binds directly to a reference
// to function
void (&g)(int) = cb;
void call(void (&f)(int))
{
  f(2);
}
template <class T>
void call_deduced(T &f)
{
  f(3);
}
int main()
{
  void (&r)(int) = cb;
  r(1);
  __CPROVER_assert(hit == 1, "local");
  call(cb);
  __CPROVER_assert(hit == 2, "parameter");
  call_deduced(cb);
  __CPROVER_assert(hit == 3, "deduced parameter");
  g(4);
  __CPROVER_assert(hit == 4, "global");
  __CPROVER_assert(hit != 4, "WRONG (must FAIL)");
}
