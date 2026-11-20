struct Outer
{
  char c;
  struct
  {
    char d;
    int i;
  } inner;
  struct
  {
    char e;
    struct
    {
      char f;
      int l;
    } nested;
  } outer_inner;
  int j;
  union
  {
    char a[5];
    int k;
  } u;
  char after_u;
};

struct Outer o;

int main()
{
  // pointer differences (unlike sizeof) are not constant expressions, so that
  // the layout of the output of dump-c is checked when that output is compiled
  // again; only char and int members are used, so that the offsets are the
  // same on all supported targets
  __CPROVER_assert((char *)&o.inner.i - (char *)&o == 8, "inner.i");
  __CPROVER_assert((char *)&o.outer_inner - (char *)&o == 12, "outer_inner");
  __CPROVER_assert(
    (char *)&o.outer_inner.nested.l - (char *)&o == 20, "nested.l");
  __CPROVER_assert((char *)&o.j - (char *)&o == 24, "j");
  // the union needs tail padding up to its alignment
  __CPROVER_assert((char *)&o.u - (char *)&o == 28, "u");
  __CPROVER_assert((char *)&o.after_u - (char *)&o == 36, "after_u");
  return 0;
}
