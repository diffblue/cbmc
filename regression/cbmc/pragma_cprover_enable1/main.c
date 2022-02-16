int main()
{
  int x;
  int y[1];

#pragma CPROVER check push
#pragma CPROVER check enable "bounds"
#pragma CPROVER check enable "signed-overflow"
  // generate assertions for the following statement
  x = x + y[1];
#pragma CPROVER check pop
  // but do not generate assertions for this one
  x = y[1];
  return x;
}
