int main()
{
  int x = 0;
  __auto_type b = x;

  // gcc: error: redeclaration of 'b' with no linkage.
  // Two genuine __auto_type declarations of the same name must be rejected,
  // even though each is internally typechecked as typeof(x) plus an
  // initializer copy of x.
  __auto_type b = x;

  return b;
}
