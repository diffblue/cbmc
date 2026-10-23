// N5008 [temp.inst]/1-2, [dcl.fct]/12: a class template specialization named
// while one of its arguments is only declared (`tree<late> make();' and a
// definition using `tree<late>' before `late' is complete) is instantiated
// as far as the context requires -- a function DECLARATION's return type
// requires nothing.  The eager instantiation failed on `sizeof(late)' in the
// node's storage buffer and (a) escaped the type checker ("Unknown exception
// type!"), or (b) left the member function templates of the rolled-back
// instance with unresolved parameter types (`key(const node_t &)' with the
// typedef kept lazily), so every call to them found no match.  libstdc++
// 16's std::set<late> / _Rb_tree_node<late> shape.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct membuf
{
  alignas(T) unsigned char storage[sizeof(T)];
  void *addr()
  {
    return static_cast<void *>(&storage);
  }
  const void *addr() const
  {
    return static_cast<const void *>(&storage);
  }
  T *ptr()
  {
    return static_cast<T *>(addr());
  }
  const T *ptr() const
  {
    return static_cast<const T *>(addr());
  }
};
struct node_base
{
  int color;
  node_base *parent;
};
template <class V>
struct node : node_base
{
  membuf<V> storage;
  V *valptr()
  {
    return storage.ptr();
  }
  const V *valptr() const
  {
    return storage.ptr();
  }
};
template <class K>
struct tree
{
  typedef node_base *base_ptr;
  typedef node<K> node_t;
  typedef node_t *node_ptr;
  static const K &key(const node_t &n)
  {
    return *n.valptr();
  }
  static const K &key(base_ptr x)
  {
    return key(static_cast<const node_t &>(*x));
  }
  static const K &key_p(node_ptr x)
  {
    return key(*x);
  }
  node_ptr root;
  tree() : root(nullptr)
  {
  }
  void insert(const K &v)
  {
    root = new node_t;
    *root->valptr() = v;
  }
  int first() const
  {
    return key(static_cast<base_ptr>(root)).v + key_p(root).v;
  }
};
class late;
tree<late> make_tree();
inline tree<late> wrap()
{
  tree<late> t;
  return t;
}
class late
{
public:
  int v;
};
tree<late> make_tree()
{
  tree<late> t;
  t.insert(late{3});
  return t;
}
int main()
{
  tree<late> t = make_tree();
  __CPROVER_assert(t.first() == 6, "tree of a class completed later");
  __CPROVER_assert(t.first() == 7, "WRONG (must FAIL)");
}
