void main(void)
{
  const int s_map_data[] = {2, 10, 20, 100, 110};

  int *p_map_x = &s_map_data[1];
  int *p_map_y = p_map_x + 1; // assertion failed here
}
