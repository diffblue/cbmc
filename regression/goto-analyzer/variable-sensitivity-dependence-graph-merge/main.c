void cal(void)
{
}

const int g_N = 5;
int x = 0;

struct
{
  int idx;
} s_str = {0};

void main(void)
{
  for(int i = 0; i < g_N; i++)
  {
    cal();
    s_str.idx = s_str.idx + 1;
  }

  __CPROVER_assert(s_str.idx > 1, "s_str.idx > 1");
}
