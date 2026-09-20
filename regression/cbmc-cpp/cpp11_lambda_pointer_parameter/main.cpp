// User-reported Issue 11.  N5008 [dcl.fct]/5, [dcl.meaning]: a parameter's
// type is the decl-specifier type as modified by its declarator.  The
// lambda's operator() took the decl-specifier type alone, so a pointer
// parameter lost its pointer: `[](W *win) { return win->soc; }' saw a `W'
// ("operand of unary * is not a pointer").  Array and function
// parameters are adjusted to pointers ([dcl.fct]/5).
extern "C" void __CPROVER_assert(bool, const char *);
struct W
{
  int soc;
};
int twice(int x)
{
  return 2 * x;
}
int main()
{
  W w{4};
  int k = 3;
  int arr[3] = {1, 2, 3};
  int *pa[2] = {&k, &k};
  auto f = [](W *win) { return win->soc; };
  auto g = [](W *win) { return (*win).soc; };
  auto h = [](W &win) { return win.soc; };
  auto a = [](int *p) { return *p; };
  auto ac = [](const W *const win) -> int { return win->soc; };
  auto pp = [](int **p) { return **p; };
  auto ga = [](auto *p) { return *p; };
  auto ra = [](int(&r)[3]) { return r[2]; };
  auto ap = [](int *p[2]) { return *p[1]; };
  auto fp = [](int (*fn)(int), int x) { return fn(x); };
  auto cap = [&](W *win) { return win->soc + k; };
  __CPROVER_assert(
    f(&w) == 4 && g(&w) == 4 && h(w) == 4, "W *, (*win).soc, W &");
  __CPROVER_assert(a(&k) == 3 && ac(&w) == 4, "int *, const W *const");
  int *kp = &k;
  __CPROVER_assert(
    pp(&kp) == 3 && ga(&k) == 3 && ga(&w.soc) == 4, "int **, auto *");
  __CPROVER_assert(
    ra(arr) == 3 && ap(pa) == 3 && fp(twice, 5) == 10,
    "reference to array, array of pointers, function pointer");
  __CPROVER_assert(cap(&w) == 7, "with a capture");
  return 0;
}
