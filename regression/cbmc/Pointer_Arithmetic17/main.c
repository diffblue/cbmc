struct dummy
{
  int *array;
};

struct cont
{
  struct dummy **array;
};

int main()
{
  struct cont cont;
  struct dummy dummy;
  struct dummy *dummies[10];
  int a[10];
  int i = 4;
  a[i] = i;
  dummy.array = &a[i - 1];
  dummies[i + 1] = &dummy;
  cont.array = &dummies[1];
  struct dummy *tmp = cont.array[i];
  int *pa = &(cont.array[i]->array[1]);
  int *pb = &(tmp->array[1]);
  __CPROVER_assert(pa == pb, "temporary should not matter");
  __CPROVER_assert(*pa == 4, "value must be 4");
  return 0;
}
