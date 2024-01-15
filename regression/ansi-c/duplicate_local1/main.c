// duplicate globals are accepted by compilers
int x;
int x;

int main()
{
  int a = 10;

  // gcc: error: redeclaration of 'a' with no linkage
  int a;

  a++;

  return 0;
}
