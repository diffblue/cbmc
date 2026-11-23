void myfunc(int *p)
{
  int x = 1;
  *p = 2; // can't point to x
  __CPROVER_assert(x == 1, "property 1");
}

int main()
{
  int *p;
  myfunc(p);
}
