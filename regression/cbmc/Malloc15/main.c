void *malloc(int);

int main()
{
  int *p;

  p = malloc(sizeof(int));
  unsigned int r = p;
  if (r != 0)
    *p = 1;    

  if (p != 0)
    __CPROVER_assert (*p == 1, "malloc");
  return 0;
}
