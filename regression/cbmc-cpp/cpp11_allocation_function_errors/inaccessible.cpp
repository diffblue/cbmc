#include <cstddef>
class C
{
  void *operator new(std::size_t);

public:
  int v;
};
int main()
{
  C *c = new C;
  (void)c;
  return 0;
}
