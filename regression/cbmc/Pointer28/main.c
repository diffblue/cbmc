int main()
{
  int *p = (int *)4;
  __CPROVER_allocated_memory(4, sizeof(int));
  int i;
  int **q;
  char *pp;

  *p = 0x01020304;
  __CPROVER_assert(*p == 0x01020304, "*p==0x01020304");
  __CPROVER_assert(p != 0, "p!=0");

  pp = (char *)p;
  __CPROVER_assert(pp[0] == 4, "byte-wise *p (0)");
  __CPROVER_assert(pp[1] == 3, "byte-wise *p (1)");
  __CPROVER_assert(pp[2] == 2, "byte-wise *p (2)");
  __CPROVER_assert(pp[3] == 1, "byte-wise *p (3)");

  p = (int *)i;
  if(i == 0)
    __CPROVER_assert(p == 0, "i==0 => p==NULL");

  q = (int **)8;
  __CPROVER_allocated_memory(8, sizeof(int *));
  *q = &i;
  **q = 0x01020304;
  __CPROVER_assert(i == 0x01020304, "**q");
}
