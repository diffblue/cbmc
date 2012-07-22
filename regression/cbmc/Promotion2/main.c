int main()
{
  // some exotic promotions

  unsigned __CPROVER_bitvector[64] bv64var;
  unsigned __CPROVER_bitvector[69] bv69var;
 
  assert(sizeof(bv64var+bv69var)==sizeof(bv69var));

  int i;
  unsigned __CPROVER_bitvector[300] bv300var;
 
  assert(sizeof(i+bv300var)==sizeof(bv300var));

  _Bool b;
  unsigned __CPROVER_bitvector[2] bv2var;
 
  assert(sizeof(b+bv2var)==sizeof(int));
}
