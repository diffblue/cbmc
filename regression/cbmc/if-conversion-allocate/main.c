int main()
{
  _Bool c;
  int *p = 0;
  if(c)
    p = __CPROVER_allocate(sizeof(int), 0);
  if(p)
    *p = 1;
  __CPROVER_assert(c || p == 0, "p only allocated if c");
  return 0;
}
