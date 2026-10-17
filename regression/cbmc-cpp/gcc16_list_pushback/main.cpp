// GCC 16's <list> implementation causes CBMC to time out.
#include <list>
int main()
{
  std::list<int> l;
  l.push_back(42);
}
