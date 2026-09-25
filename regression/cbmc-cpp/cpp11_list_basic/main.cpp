// std::list operations (push_back / push_front / size / front / back /
// iteration).  The list node is created by the variadic template member
// _M_create_node, whose body constructs an RAII guard
// `std::__allocated_ptr<_Alloc> __guard{__alloc, __p}`.  __allocated_ptr has
// user-provided constructors, so this braced-init-list must invoke a
// constructor ([dcl.init.list]/3), not member-wise aggregate initialization.
// CBMC previously misclassified the (not-yet-elaborated) class template
// specialization as a POD and aggregate-initialized it, which cleared
// _M_create_node's body and left every list node nondet.
#include <list>

int main()
{
  std::list<int> l;
  l.push_back(1);
  l.push_back(2);
  l.push_front(3);

  __CPROVER_assert(l.size() == 3, "size after pushes");
  __CPROVER_assert(l.front() == 3, "front element");
  __CPROVER_assert(l.back() == 2, "back element");

  int sum = 0;
  for(std::list<int>::iterator it = l.begin(); it != l.end(); ++it)
    sum += *it;
  __CPROVER_assert(sum == 6, "iteration visits all elements");
  return 0;
}
