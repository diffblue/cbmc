int main()
{
  int a[5];
  
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<5) ==> a[i]==i+1});

  assert(a[0]==1);
  assert(a[1]==2);
  assert(a[2]==3);
  assert(a[3]==4);
  assert(a[4]==5);
  return 0;                
}
