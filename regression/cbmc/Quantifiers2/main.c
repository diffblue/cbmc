int main()
{
  int a[10];
  int b[2];
  int c[10];
  int d[2];
  // C# style
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<10) ==> a[i]>=1 && a[i]<=10 });
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<10) ==> b[i]>=1 && b[i]<=10 });
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<10) ==> c[i]==100 });
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<10) ==> d[i]==1000 });

  __CPROVER_assert(__CPROVER_forall {unsigned i; (i>=0 && i<10) ==> a[i]>=1 && a[i]<=10}, "forall a[]");
  __CPROVER_assert((b[0]>=1 && b[0]<=10) || (b[1]>=1 && b[1]<=10), "1st exists b[]");
  __CPROVER_assert((b[0]>=1 && b[0]<=10) && (b[1]>=1 && b[1]<=10), "2nd exists b[]");
  __CPROVER_assert(__CPROVER_forall {int i; (i>=1 && i<=10) ==> c[i-1]==100}, "1st forall c[]");
  __CPROVER_assert(__CPROVER_forall {int i; (i>=1 && i<=10) ==> c[i]==100}, "2nd forall c[]");
  __CPROVER_assert(d[0]==1000 || d[1]==1000, "exists d[]");
  return 0;                
}
