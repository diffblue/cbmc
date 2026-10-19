// clang-format off
void w(int *p)
{
  *p = 1;
}

int main()
{
  int s;
  for(int j = 0; j < 3; j++)
    __CPROVER_loop_invariant(0 <= j && j <= 3)
  {
    for(int i = 0; i < 3; i++)
      __CPROVER_loop_invariant(0 <= i && i <= 3)
    {
      w(&s);
    }
  }
}
// clang-format on
