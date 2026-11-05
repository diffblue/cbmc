struct Outer
{
  char c;
#pragma pack(push, 1)
  struct
  {
    char d;
    int i;
  } inner;
#pragma pack(pop)
  int j;
};

int main()
{
  struct Outer o;
  // not a constant expression, so that the layout of the output of dump-c is
  // checked when that output is compiled again
  long offset = (char *)&o.j - (char *)&o;
  __CPROVER_assert(offset == 8, "inner is packed");
  return 0;
}
