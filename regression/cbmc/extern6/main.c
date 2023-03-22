extern int stuff[];

extern int a[];
int a[] = {1, 2, 3};

int main()
{
  unsigned char idx;
  long val = *(long *)(stuff + idx);
  __CPROVER_assert(val == 13, "compare");
  return 0;
}
