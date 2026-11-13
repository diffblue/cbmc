extern "C" void __CPROVER_assert(bool, const char *);
int hit;
// [dcl.typedef]/2: a member alias-declaration of function type (libc++'s
// __stop_callback_base::__callback_fn_t)
struct B
{
  using F = void(B *, int) noexcept;
  F *f;
};
void cb(B *, int k) noexcept
{
  hit = k;
}
template <class T>
struct W
{
  using G = void(T, const char *);
  G *g;
};
void cw(int k, const char *)
{
  hit = k;
}
int main()
{
  B b{cb};
  b.f(&b, 1);
  __CPROVER_assert(hit == 1, "member alias");
  W<int> w;
  w.g = &cw;
  w.g(2, "x");
  __CPROVER_assert(hit == 2, "member alias of a class template");
  __CPROVER_assert(hit != 2, "WRONG (must FAIL)");
}
