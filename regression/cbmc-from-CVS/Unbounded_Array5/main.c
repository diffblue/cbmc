int mem[__CPROVER_constant_infinity_uint];

int  main()
{
  int i, j, mem_j;
  
  mem[0] = 0;
  mem[1] = 1;

  mem[j] = 1;
  mem_j = mem[j];
  assert(mem_j == 1);

  mem[i] = mem[mem_j];
   
  unsigned xxxi=mem[i];
  unsigned xxx1=mem[1];

  __CPROVER_assert(xxxi == xxx1, "Check infinite mem");
}
