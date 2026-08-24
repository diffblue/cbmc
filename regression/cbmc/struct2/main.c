struct T
{
  // intentionally empty to trigger struct-prefix handling in the analysis
  // (empty structs are a GCC-only feature)
};

struct S
{
  struct T t;
  int other;
};

void foo(struct S s2)
{
  struct T *p = &s2.t;
  struct T t2 = *p;
  __CPROVER_assert(0, "");
}

int main()
{
  struct S s;
  foo(s);
}
