extern "C" void __CPROVER_assert(bool, const char *);
struct holder
{
  int *p = nullptr;
  holder()
  {
  }
  holder(const holder &o) : p(o.p)
  {
  }
};
enum kind_t
{
  KIND_A,
  KIND_B
};
struct rec
{
  int z = 7;
};
struct S
{
  enum kind_t kind;
  int count;
  holder h;
  rec extra = {};
  bool flag;
};
S make()
{
  return {.count = 3};
}
int main()
{
  S s;
  s = (struct S){.kind = KIND_B, .flag = true};
  __CPROVER_assert(
    s.kind == KIND_B && s.count == 0 && s.extra.z == 7 && s.flag,
    "compound literal");
  S t = (S){.count = 2};
  __CPROVER_assert(t.kind == KIND_A && t.count == 2, "initialization");
  S u = make();
  __CPROVER_assert(u.count == 3 && u.extra.z == 7, "return");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
