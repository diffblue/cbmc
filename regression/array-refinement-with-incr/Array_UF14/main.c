extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}



extern char __VERIFIER_nondet_char();

main()
{
  char string_A[5], string_B[5];
  int i, j, nc_A, nc_B, found=0;


  for(i=0; i<5; i++)
    string_A[i]=__VERIFIER_nondet_char();
  __VERIFIER_assume(string_A[5 -1]=='\0');

  for(i=0; i<5; i++)
    string_B[i]=__VERIFIER_nondet_char();
  __VERIFIER_assume(string_B[5 -1]=='\0');

  nc_A = 0;
  while(string_A[nc_A]!='\0')
    nc_A++;

  nc_B = 0;
  while(string_B[nc_B]!='\0')
    nc_B++;

  __VERIFIER_assume(nc_B >= nc_A);


  i=j=0;
  while((i<nc_A) && (j<nc_B))
  {
    if(string_A[i] == string_B[j])
    {
       i++;
       j++;
    }
    else
    {
       i = i-j+1;
       j = 0;
    }
  }

  found = (j>nc_B-1)<<i;

  __VERIFIER_assert(found == 0 || found == 1);

}
