// clang-format off
int a[10];

int main()
{
  for(int i = 0; i < 10; i++)
    __CPROVER_assigns(i, __CPROVER_object_whole(a))
    __CPROVER_loop_invariant(0 <= i && i <= 10)
  {
    a[i] = 0;
  }

  int *p = a;
  for(int k = 0; k < 10; k++)
    __CPROVER_loop_invariant(0 <= k && k <= 10)
  {
    *(p + k) = 1;
  }
}
// clang-format on
