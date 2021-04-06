int main()
{
#ifdef __GNUC__
  int x = 1;
  if(x == 0)
  {
    __CPROVER_assert(0, "");
    // __builtin_types_compatible_p yields a proper "bool" typed constant
    __CPROVER_assume(__builtin_types_compatible_p(double, float));
  }
#endif
  return 0;
}
