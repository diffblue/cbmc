int nondet_bool(void);

int increment(int x)
{
  if(nondet_bool())
    x++;
  else
    x += 6;
  return x;
}

int main()
{
  int x = 42;
  x++;
  int y = increment(x);
  y--;
  return 0;
}
