int g_a[4];
#define SZ(a)   sizeof(a)/sizeof(a[0])
const int g_a_SZ = SZ(g_a);

void reset(void)
{
  int i;
  for (i=0; i < g_a_SZ; i++)    //  4 times
    g_a[i] = 0;
}

int main()
{
  reset();
}

