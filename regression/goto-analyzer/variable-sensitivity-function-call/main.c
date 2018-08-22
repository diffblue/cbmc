int f(const int *y);

extern const int g_map[];

int g_out1;
int g_out2;

extern int g_in;
// int g_in;

void main(void)
{
  int t1;
  int t2;

  t1 = 5;
  t2 = f(g_map);

  __CPROVER_assert(t1 == 5, "t1 == 5 after calling function with missing body");
}
