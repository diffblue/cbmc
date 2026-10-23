extern "C" void __CPROVER_assert(bool, const char *);
// a non-POD class (a member with a user-declared, but not user-provided,
// constructor) whose own default constructor is implicitly declared
struct Long
{
  Long() = default;
  long cap;
};
struct S
{
  int x;
  Long l;
};
// a default constructor explicitly defaulted on its first declaration is
// not user-provided either ([dcl.fct.def.default]/5)
struct D
{
  int x;
  D() = default;
};
// a user-provided default constructor: no zero-initialization
struct UP
{
  int x;
  UP()
  {
  }
};
int main()
{
  S a = S();
  __CPROVER_assert(a.x == 0 && a.l.cap == 0, "S(): zero-initialized");
  S b = S{};
  __CPROVER_assert(b.x == 0 && b.l.cap == 0, "S{}: zero-initialized");
  S c{};
  __CPROVER_assert(c.x == 0 && c.l.cap == 0, "S c{}: zero-initialized");
  S d = {};
  __CPROVER_assert(d.x == 0 && d.l.cap == 0, "S d = {}: zero-initialized");
  S *p = new S();
  __CPROVER_assert(p->x == 0 && p->l.cap == 0, "new S(): zero-initialized");
  S *q = new S{};
  __CPROVER_assert(q->x == 0 && q->l.cap == 0, "new S{}: zero-initialized");
  D e = D();
  __CPROVER_assert(e.x == 0, "defaulted default constructor: zero-initialized");
  // no zero-initialization: `UP()' runs only the user-provided constructor
  // and `S f;' default-initializes, so both values are indeterminate
  UP u = UP();
  S f;
  u.x = 1;
  f.x = 2;
  __CPROVER_assert(u.x + f.x == 3, "after assignment");
  __CPROVER_assert(a.x == 1, "WRONG (must FAIL)");
}
