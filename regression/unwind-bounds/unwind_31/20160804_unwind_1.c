int g_a[4];
#define SZ(a)   sizeof(a)/sizeof(a[0])

void reset(void)
{
  int i;
  for (i=0; i < SZ(g_a); i++)  // 4 times
    g_a[i] = 0;
}

int main() {
  reset();
}

