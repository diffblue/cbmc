// guard expression includes global variable.

extern int g_n;
extern int g_a[];
int calc(void)
{
  int i;
  int s = 0;
  for (i=0; i < g_n; i++)
    s += g_a[i];
  return s;
}

int main() {
  calc();
}

