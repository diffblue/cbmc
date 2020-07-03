int f2(int, const int *);
extern const int g_map[];

int g_out1;
int g_out2;

extern int g_in;

void main(void)
{
  int t1;
  int t2;

  t1 = g_in;
  t2 = f2(t1, g_map);

  if(t2 >= 0)
    g_out1 = t2;
  else
    g_out1 = 0;

  g_out2 = t1;
}
