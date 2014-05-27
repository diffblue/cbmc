int foo();

int bar(int a, int b);

int main()
{
  _Bool x;
  return (x?foo:bar)(x, x);
}
