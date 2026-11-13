extern "C" void __CPROVER_assert(bool, const char *);
template <class>
struct node;
template <class>
struct node_base;
template <class P>
struct ptr_traits;
template <class T>
struct ptr_traits<T *>
{
  template <class U>
  using rebind = U *;
};
// libc++'s __rebind_pointer_t: the pointer alias reached through a member
// template-id of another class ([temp.alias]/2, [temp.inst]/2)
template <class From, class To>
using rebind_pointer_t = typename ptr_traits<From>::template rebind<To>;
template <class VoidPtr>
struct node_traits
{
  typedef rebind_pointer_t<VoidPtr, node<VoidPtr>> node_pointer;
  typedef rebind_pointer_t<VoidPtr, node_base<VoidPtr>> link_pointer;
};
template <class VoidPtr>
struct node_base
{
  typedef typename node_traits<VoidPtr>::link_pointer link_pointer;
  link_pointer next = nullptr;
};
template <class VoidPtr>
struct node : node_base<VoidPtr>
{
  int value = 0;
  typename node_base<VoidPtr>::link_pointer as_link()
  {
    return this;
  }
};
int main()
{
  node_base<void *> end;
  node<void *> n;
  n.value = 3;
  end.next = n.as_link();
  __CPROVER_assert(
    static_cast<node<void *> *>(end.next)->value == 3, "linked node");
  __CPROVER_assert(end.next == nullptr, "WRONG (must FAIL)");
}
