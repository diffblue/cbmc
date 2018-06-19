int main()
{
  unsigned int i=2;
  __CPROVER_assert(0l==(signed long int)(i - (unsigned int)2),
                   "difference of cast");
  return 0;
}
