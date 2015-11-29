// this exposes a problem with the renaming of "ignore"
// due to the inlining

unsigned short g;

inline void baz()
{
  unsigned short ignore;
  ignore=g;
  // should fail
  __CPROVER_assert(0, "KABOOM");
}

static void foo()
{
    baz();
}

static void bar()
{
    baz();
}

int main()
{
  g=0;
  foo();

  g=1;
  bar();       

  return 0;
}
