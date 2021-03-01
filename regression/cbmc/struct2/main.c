struct T
{
  // intentionally empty to trigger is_prefix_of code (empty structs, however,
  // are a GCC-only feature)
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
