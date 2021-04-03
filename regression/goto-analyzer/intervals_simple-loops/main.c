const int g_N = 2;

void main(void)
{
  for(int i = 0; i < g_N; i++)
  {
    __CPROVER_assert(0, "assertion 0");
  }

  for(int j = 4; j >= g_N; j--)
  {
    __CPROVER_assert(0, "assertion 0");
  }
}
