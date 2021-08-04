int nondet_bool(void);

int main()
{
  int x = 0;
  x = nondet_bool() ? (x + 1) : (x + 2);

  int y = 0;
  y = nondet_bool() ? (y + 1) : (y - 1);
}
