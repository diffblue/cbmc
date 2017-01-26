
int g_a0[4];
int g_a1[3];

struct {
  int sz;
  int*data;
} g_ram[] = {{ 4, g_a0 }, {3, g_a1}};

void reset_all(void)
{
  int i, j;
  for (i=0; i < 2; i++)
    for (j=0; j<g_ram[i].sz; j++)   // 4, 3 times
      g_ram[i].data[j] = 0;
}

int main()
{
  reset_all();
  return 0;
}

