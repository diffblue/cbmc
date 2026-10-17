extern "C" void __CPROVER_assert(bool, const char *);
template <class>
struct node;
template <class>
struct node_base;
struct ptr_traits
{
  template <class U>
  using rebind = U *;
};
template <class>
struct node_traits
{
  // U * does not require U to be complete: node<void> must not be
  // instantiated here, while node_base<int> is being instantiated
  typedef ptr_traits::rebind<node<void>> node_pointer;
  typedef ptr_traits::rebind<node_base<int>> link_pointer;
};
template <class>
struct node_base
{
  typedef node_traits<int>::link_pointer link_pointer;
  link_pointer next = nullptr;
};
template <class>
struct node : node_base<int>
{
  int value = 0;
  link_pointer as_link()
  {
    return this;
  }
};
int main()
{
  node_base<int> end;
  node<void> n;
  n.value = 3;
  end.next = n.as_link();
  __CPROVER_assert(
    static_cast<node<void> *>(end.next)->value == 3, "linked node");
  __CPROVER_assert(end.next == nullptr, "WRONG (must FAIL)");
}
