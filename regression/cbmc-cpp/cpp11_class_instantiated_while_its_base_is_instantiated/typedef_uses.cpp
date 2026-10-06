// N5008 [temp.inst]/1-2: a member typedef naming a class template
// specialization does not instantiate it; a later use whose semantics
// depend on the class does: a derived-to-base pointer conversion
// ([conv.ptr]/3) and list-initialization of an initializer_list element
#include <initializer_list>
extern "C" void __CPROVER_assert(bool, const char *);
struct node_base
{
  int color = 1;
};
template <class V>
struct node : node_base
{
  V value;
};
struct iterator
{
  typedef node<int> *link_type;
  int color_of(link_type x)
  {
    node_base *b = x;
    return b->color;
  }
};
template <class A, class B>
struct pr
{
  A first;
  B second;
  pr(const A &a, const B &b) : first(a), second(b)
  {
  }
};
template <class K, class V>
struct mp
{
  typedef pr<const K, V> value_type;
};
int count(std::initializer_list<mp<int, long>::value_type> il)
{
  return int(il.size());
}
int main()
{
  node<int> n;
  iterator it;
  __CPROVER_assert(it.color_of(&n) == 1, "derived-to-base conversion");
  __CPROVER_assert(count({{1, 2L}, {3, 4L}}) == 2, "initializer_list element");
  __CPROVER_assert(count({{1, 2L}}) == 2, "WRONG (must FAIL)");
}
