int main() {
  unsigned x;
  int i;
  int a[100];

  // this is guaranteed not to be a buffer overflow  
  if(x<100 && a[x])
  {
    i++;
  }

  __CPROVER_assume(i<100);

  // this is guaranteed not to be a buffer underflow
  if(i>=0 && a[i])
  {
    i++;
  }
}
