struct B
{
  int bi;
  int *c;
};

struct A
{
  int ai;
  struct B b;
};

int main()
{
  struct A *a;
  if((&a->b)->c == 0)
    return 1;
  return 0;
}
