// guard expression includes arguments.

int g_a0[4];
int g_a1[3];

struct {
  int sz;
  int*data;
} g_ram[] = {{ 4, g_a0 }, {3, g_a1}};

void reset(int t_id)
{
  int j;
  for (j=0; j<g_ram[t_id].sz; j++)
  g_ram[t_id].data[j] = 0;
}

int main() {
  reset(0);
}

