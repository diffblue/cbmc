int nondet_bool(void);

int main()
{
  int x;
  x = nondet_bool() ? (x + 1) : (x + 2);

  int y;
  y = nondet_bool() ? (y + 1) : (y - 1);
}
