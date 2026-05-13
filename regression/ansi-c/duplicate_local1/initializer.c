int main()
{
  int a = 10;

  // gcc: error: redeclaration of 'a' with no linkage, also when the second
  // declaration has an initializer
  int a = 20;

  return a;
}
