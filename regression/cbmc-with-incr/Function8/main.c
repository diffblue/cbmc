// this exposes a problem with the renaming of "ignore"
// due to the inlining

inline void baz(unsigned short ignore)
{
  // should fail
  __CPROVER_assert(0, "KABOOM");
}

static void foo()
{
  baz(1);
}

static void bar()
{
  baz(0);
}

int main()
{
  foo();

  bar();       

  return 0;
}
