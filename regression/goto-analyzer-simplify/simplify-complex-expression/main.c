int nondet_int(void);

int main(void)
{
  int r = nondet_int();
  r = r + 1;
  if(r == 2)
  {
    return 1;
  }
  return 0;
}
