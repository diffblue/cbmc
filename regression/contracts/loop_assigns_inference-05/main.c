// clang-format off
struct S
{
  int f;
};

void w(struct S *p)
{
  p->f = 1;
}

int main()
{
  struct S s;
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
