void main()
{
  int a[2];
#pragma CPROVER check push
#pragma CPROVER check enable "bounds"
  a[0] = 1;
  a[1] = 2;
  a[2] = 3;
#pragma CPROVER check pop
}
