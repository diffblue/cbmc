#define LIMIT 10

void main ()
{
  int a[LIMIT];

  for (int i = 0; i < LIMIT; ++i) {
    a[i] = i;
  }

  int x;
  int y;

  __CPROVER_assume(0 <= x && x < LIMIT);
  __CPROVER_assume(0 <= y && y < LIMIT);
  __CPROVER_assume(x + y < LIMIT);

  assert(a[x] + a[y] == x + y);

  return 1;
}
