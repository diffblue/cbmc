#include <cassert>

template <class T>
struct C
{
  static const char* k;
};

template <typename T>
const char* C<T>::k = "C";

int main(int argc, char* argv[])
{
  assert(C<int>::k[0] == 'C');
  assert(C<char>::k[0] == 'C');
  assert(&C<int>::k != &C<char>::k);
  return 0;
}
