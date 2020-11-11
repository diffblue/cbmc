extern int g_in;

int g_a[3];

int g_out1;

void main(void)
{
  int i;

  g_a[0] = 1;
  g_a[1] = 2;
  g_a[2] = 3;

  i = 0;
  if(g_in > 0)
  {
    i = 1;
    g_a[2] = g_a[1];
  }

  g_out1 = g_a[i];
}
