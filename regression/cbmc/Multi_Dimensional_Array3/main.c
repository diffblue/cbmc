unsigned int nondet_uint();

typedef int *iptr;

int x, y, z;

int main()
{
  // this checks whether the alias analysis can
  // track pointers in multi-dimensional arrays
  
  iptr array[3][3]={{&x,0,0},{&y,0,0},{&z,0,0}};

  unsigned int a, b;
  a = nondet_uint();
  b = nondet_uint();
  __CPROVER_assume (a < 3 && b < 3);

  array[a][b] = &z;
  
  iptr p;
  p=array[a][b];

  *p=1;
  
  assert(z==1);
}
/* end of case 2 */
