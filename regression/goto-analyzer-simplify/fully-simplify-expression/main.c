unsigned int nondet_uint();

int main(void)
{
  unsigned int K = nondet_uint();
  unsigned int x = 0u;
  unsigned int result = K * x;
  return 0;
}