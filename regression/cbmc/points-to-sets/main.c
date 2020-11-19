int main()
{
  unsigned int value;
  int *p = (int *)value;

  *p = *p + 1;
  assert(1);
  return 0;
}
