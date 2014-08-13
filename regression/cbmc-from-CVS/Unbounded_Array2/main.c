unsigned int nondet_uint();
_Bool nondet_bool();

int main() {
  unsigned int n=nondet_uint();
  _Bool x=nondet_bool();
  int a[n];
  
  __CPROVER_assume(n>10 && n<100000);
  
  if(x)
    a[0]=1;

  a[1]=2;

  assert(a[0]==1 || !x); 
}
