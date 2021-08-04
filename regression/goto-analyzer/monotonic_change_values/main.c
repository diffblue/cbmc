int nondet(void);

int main()
{
  int x = 42;
  x++;
  x = x + 2;

  int y = 42;
  y--;
  y = y - 2;

  int z = (y + 1729) * (x - 6);
  z++;
  z--;

  int u = nondet();
  u++;
  u *= 2;

  return 0;
}
