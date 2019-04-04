int main()
{
  int x;
  int y[1];

#pragma CPROVER check push
#pragma CPROVER check disable "bounds"
#pragma CPROVER check disable "signed-overflow"
  // do not generate assertions for the following statement
  x = x + y[1];
  // pop all annotations
#pragma CPROVER check pop
  // but do generate assertions for this one
  x = y[1];
  return x;
}
