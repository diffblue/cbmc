// N5008 [temp.variadic]/5 + [over.match.ctor]: forwarding a pack of
// TWO class-type rvalues into a nested class's constructor
// (`scoped s(this, forward_<Args>(args)...)`) selects the WRONG
// overload -- the 2-parameter (node*, alloc_base*) constructor
// instead of the variadic allocating one -- so the node is never
// constructed.  This is libstdc++ _Hashtable::_M_emplace's
// _Scoped_node: the emplaced pair<key,value> stays UNINITIALIZED,
// the duplicate check compares garbage, and a same-key emplace
// wrongly inserts (unordered_map::emplace wrong-code,
// cpp17_umap_emplace_mixed_categories).  Discriminants established:
// TWO class-type rvalues required (one passes; scalars pass);
// braces vs parens irrelevant.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T> struct remove_ref { typedef T type; };
template <class T> struct remove_ref<T &> { typedef T type; };
template <class T> struct remove_ref<T &&> { typedef T type; };
template <class T>
T &&forward_(typename remove_ref<T>::type &t)
{
  return static_cast<T &&>(t);
}
template <class T>
T &&forward_(typename remove_ref<T>::type &&t)
{
  return static_cast<T &&>(t);
}
struct key
{
  key() : no(0) {}
  unsigned no;
};
struct val
{
  val() : x(0) {}
  int x;
};
struct node
{
  int stored;
};
struct alloc_base
{
  node storage;
  template <class... Args> node *make(Args &&... a)
  {
    storage.stored = sizeof...(Args);
    return &storage;
  }
};
template <class T> struct table : alloc_base
{
  struct scoped
  {
    scoped(node *n, alloc_base *h) : n_(n), h_(h)
    {
    }
    template <class... Args>
    scoped(alloc_base *h, Args &&... a)
      : n_(h->make(forward_<Args>(a)...)), h_(h)
    {
    }
    node *n_;
    alloc_base *h_;
  };
  template <class... Args> int emp(int, Args &&... args)
  {
    scoped s(this, forward_<Args>(args)...);
    return s.n_->stored;
  }
  template <class... Args> int emplace(Args &&... args)
  {
    return emp(1, forward_<Args>(args)...);
  }
};
int main()
{
  table<int> t;
  __CPROVER_assert(t.emp(1, key{}, val{}) == 2, "variadic ctor selected");
  return 0;
}
