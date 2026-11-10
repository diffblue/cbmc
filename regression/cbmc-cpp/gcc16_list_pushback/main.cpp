// std::list<int>::push_back with GCC 16's <list>
#include <list>
int main()
{
  std::list<int> l;
  l.push_back(42);
}
