// C++11 braced-init-list in member initializers
struct Base
{
  int a;
  int b;
};

struct S : Base
{
  int c;
  S(int x, int y, int z) : Base{x, y}, c(z)
  {
  }
};

int main()
{
  S s(1, 2, 3);
  return 0;
}
