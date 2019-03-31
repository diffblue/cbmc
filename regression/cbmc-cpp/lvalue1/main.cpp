#include <cassert>
enum asd
{
  ASD,
  ABC
};

int main()
{
  asd a = ASD, b = ASD;

  // casts to references are lvalues
  asd &c = (asd &)((int &)a |= (int &)b);
  assert(a == ASD);
  c = ABC;
  assert(a == ABC);

  // in C++, comma expressions are lvalues
  (a, b) = ASD;
}
