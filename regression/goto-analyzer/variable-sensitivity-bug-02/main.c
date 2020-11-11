// map.c
int map(int t_x, int *p_map) // mismatch :(
{
  int n = p_map[0];
  int *p_map_x = &p_map[1];
  int *p_map_y = p_map_x + n; // assertion failed here
  int i;

  if(t_x < p_map_x[0])
    return p_map_y[0];

  for(i = 1; i < n; i++)
    if(t_x < p_map_x[i])
    {
      int x0 = p_map_x[i - 1];
      int x1 = p_map_x[i];
      int y0 = p_map_y[i - 1];
      int y1 = p_map_y[i];
      return (y1 - y0) / (x1 - x0) * (t_x - x0) + y0;
    }

  return p_map_y[n - 1];
}

/// file2.c
int map(int t_x, volatile const int *p_map);
volatile const int s_map_data[] = {2, 10, 20, 100, 110};
extern int g_x;
int g_y;

void main(void)
{
  g_y = map(g_x, s_map_data);
}
