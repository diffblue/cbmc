// Dog-food kernel (src/util/get_module.cpp): iterating a
// std::list<const symbolt*> with a range-for and dereferencing the
// POINTER element with -> fails with "symbol 'operator->' is
// unknown" -- operator-> is only meaningful for class types
// ([over.ref]); for a plain pointer the built-in -> must be used.
// The range-for's element type presumably mis-derives as a class.
#include <list>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
struct symbolt
{
  std::string name;
};
int main()
{
  symbolt s{"abc"};
  std::list<const symbolt *> l;
  l.push_back(&s);
  int n = 0;
  for(const symbolt *p : l)
    n += p->name.size();
  __CPROVER_assert(n == 3, "arrow on pointer element of list range-for");
  return 0;
}
