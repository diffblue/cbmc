int main()
{
  int x = 0;
  __auto_type b = x;

  // gcc: error: redeclaration of 'b' with no linkage
  __auto_type b = x;

  return b;
}
