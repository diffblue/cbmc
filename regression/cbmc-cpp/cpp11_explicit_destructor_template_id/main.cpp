// An explicit (pseudo-)destructor call written with a template-id,
// `p->~Foo<T>()`, names the destructor of Foo<T>; the template arguments
// merely restate the class type and are not a template-id to be
// instantiated ([expr.prim.id.dtor], [class.dtor]).  Previously CBMC tried
// to instantiate `~Foo` as a template (because the name carried template
// arguments) and threw, so any function containing such a call lost its
// body.  This is libstdc++'s `__node->~_Rb_tree_node<_Val>()` in
// std::_Rb_tree::_M_construct_node (run on the exception path), which left
// _M_construct_node bodyless and the inserted node's value unconstructed.

struct Base
{
  ~Base() {}
};

template <class T>
struct Node : Base
{
  T value;
};

template <class T>
struct Wrap
{
  static void destroy(Node<T> *n) { n->~Node<T>(); }

  template <class... A>
  void build(Node<T> *n)
  {
    try
    {
      // (placeholder construction)
    }
    catch(...)
    {
      n->~Node<T>(); // explicit destructor via template-id in a member tmpl
      throw;
    }
  }
};

int main()
{
  Node<int> n;
  n.value = 5;
  Wrap<int>::destroy(&n);
  Wrap<int> w;
  w.build(&n);
  __CPROVER_assert(true, "explicit destructor via template-id type-checks");
  return 0;
}
