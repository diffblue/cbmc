extern "C" void __CPROVER_assert(bool, const char *);
int hit;
void cb(int k)
{
  hit = k;
}
// [dcl.typedef]/2: the alias-declaration has the same semantics as
// `typedef void F(int);', so F * is a pointer to function (libc++'s
// __stop_callback_base::__callback_fn_t)
using F = void(int);
struct S
{
  F *f;
  void invoke(int k)
  {
    f(k);
  }
};
int main()
{
  F *p = &cb;
  p(1);
  __CPROVER_assert(hit == 1, "pointer variable");
  S s{&cb};
  s.invoke(2);
  __CPROVER_assert(hit == 2, "pointer member");
  __CPROVER_assert(hit != 2, "WRONG (must FAIL)");
}
