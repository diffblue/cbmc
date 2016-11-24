#include <cassert>

int main()
{
  // anonymous union
  union
  {
    int a;
    char b;	
  };

  a = 'z';
  assert(b == 'z');
}
