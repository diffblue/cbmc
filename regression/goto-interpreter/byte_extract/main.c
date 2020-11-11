union U {
  int x;
  char c[sizeof(int)];
};

int main()
{
  union U u;
  // make the lowest and highest byte 1
  u.x = 1 | (1 << (sizeof(int) * 8 - 8));
  int i = u.x;
  char c0 = u.c[0];
  char c1 = u.c[1];
  char c2 = u.c[2];
  char c3 = u.c[3];

  __CPROVER_assert(u.c[0] == 1, "");

  return 0;
}
