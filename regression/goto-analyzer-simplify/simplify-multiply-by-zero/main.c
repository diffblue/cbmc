int nondet_int(void);

int main(void)
{
  int K = nondet_int();
  int x = 0;
  return K * x;
}
