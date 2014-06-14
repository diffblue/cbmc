unsigned nondet_uint();

int new_intu(unsigned int lower, unsigned int upper)
{
  unsigned int val = (unsigned) 1u << 31;

  if (val < lower)
    return lower;

  if (val > upper)
    return upper;

  return val;
}


int main()
{
  unsigned int i1 = new_intu(1u, 31u);
  assert(1 <= i1 && i1 <= 31);
}
