// clang-format off
int a[10];

int main()
{
  for(int j = 0; j < 3; j++)
    __CPROVER_assigns(j, __CPROVER_object_whole(a))
    __CPROVER_loop_invariant(0 <= j && j <= 3)
  {
    // a target with a non-constant index
    for(int i = 0; i < 10; i++)
      __CPROVER_loop_invariant(0 <= i && i <= 10)
    {
      a[i] = 0;
    }

    // a target with a non-constant offset
    int *p = a;
    for(int k = 0; k < 10; k++)
      __CPROVER_loop_invariant(0 <= k && k <= 10)
    {
      *(p + k) = j;
    }
  }
}
// clang-format on
