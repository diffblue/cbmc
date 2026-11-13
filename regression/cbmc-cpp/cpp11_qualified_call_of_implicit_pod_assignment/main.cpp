// N5008 [class.copy.assign]/2: a class without a user-declared copy
// assignment operator has one declared implicitly, and it can be named.
// libstdc++ 16's _List_node_header::_M_init assigns its _List_size base
// through `_List_size::operator=(_List_size())'.  The front end declares the
// operator only for non-POD classes (a POD is assigned bitwise), so the
// qualified name found nothing and the body of _M_init was dropped: every
// std::list built with gcc 16's headers had an uninitialized header node.
extern "C" void __CPROVER_assert(bool, const char *);
struct list_size
{
  unsigned long size = 0;
};
struct node_base
{
  node_base *next;
  node_base *prev;
};
struct header : public node_base, list_size
{
  header() noexcept
  {
    init();
  }
  void init() noexcept
  {
    this->next = this->prev = this;
    list_size::operator=(list_size());
  }
};
int main()
{
  header h;
  h.size = 7;
  h.init();
  __CPROVER_assert(
    h.size == 0 && h.next == &h,
    "implicit assignment operator called by qualified name");
}
