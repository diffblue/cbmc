typedef unsigned short uint16;

struct st
{
  uint16 data1;
} str1;

extern struct
{
  struct st data2;
} g_sts;

void func1(uint16 a)
{
  // Expect the assert to be 'Unknown' because we would expect 'a' to be TOP
  // here because p->data1 passed in as argument should be TOP.
  __CPROVER_assert(a == 0, "func1.a == 0");
}

void func2(struct st *p)
{
  func1(p->data1);
}

void main(void)
{
  const int s_map_data[] = {2, 10, 20, 100, 110};

  int *p_map_x = &s_map_data[1];
  int *p_map_y = p_map_x + 1;

  // Tests that the write_stack handles &smap_data[1]
  __CPROVER_assert(*p_map_y == 20, "*main.p_map_y == 20");

  func2(&g_sts.data2);
}
