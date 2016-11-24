typedef __CPROVER_size_t size_t;
void *malloc(size_t size);
void free(void *p);
size_t nondet_uint();

int main() {
  int *p;
  unsigned o;
  size_t n=nondet_uint();
  
  __CPROVER_assume(n>=1);
  __CPROVER_assume(n<10000000);

  p=malloc(sizeof(int)*n);
  
  o=n-1;

  p[o]=1000;
  
  assert(p[o]==1000);

  free(p);
}
