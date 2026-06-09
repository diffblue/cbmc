#include <cassert>
#include <initializer_list>

// A minimal container with an initializer-list constructor that records
// the element count and the first element, so the constructed value can
// be checked by symbolic execution (unlike std::vector, whose heap
// internals are not fully modelled).
struct bag
{
  unsigned count;
  int first;

  bag(std::initializer_list<int> l) : count(0), first(0)
  {
    for(int v : l)
    {
      if(count == 0)
        first = v;
      ++count;
    }
  }
};

// `return { ... };` must list-initialize the returned object using bag's
// initializer-list constructor ([stmt.return] + [dcl.init.list] +
// [over.match.list]/1 phase 1.1), passing the whole braced-init-list as
// a single std::initializer_list argument — NOT unwrapping a single
// element to convert it directly to bag.
bag make_single()
{
  return {42};
}

bag make_three()
{
  return {7, 8, 9};
}

int main()
{
  bag a = make_single();
  assert(a.count == 1);
  assert(a.first == 42);

  bag b = make_three();
  assert(b.count == 3);
  assert(b.first == 7);

  return 0;
}
