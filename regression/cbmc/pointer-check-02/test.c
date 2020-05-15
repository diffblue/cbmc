void main()
{
  char *p;

  {
    int i;
    __CPROVER_assume(p == &i);
  }

  *p;
}
