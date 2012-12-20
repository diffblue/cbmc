
namespace test_space {

int i;
}

int test_space::j;

void f()
{
  ::test_space::i=0;
}

namespace test_space {
  void g()
  {
    i=1;
    j=2;
  }
}

using namespace test_space;

int main()
{
  f();
  j=1;
  assert(i==0);
}
