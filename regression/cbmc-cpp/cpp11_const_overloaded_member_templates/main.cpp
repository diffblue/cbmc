// N5008 [over.load]/2.3, [over.call.func]/3, [over.match.funcs]/5: member
// templates `find(const K &)' and `find(const K &) const' are different
// members, and an unqualified call in a const member function has a const
// implied object, for which only the const one is viable.  Such a call was
// ambiguous (the caller's body was dropped), and out-of-class definitions
// were attached to the instances by name and arity alone, so the const
// member ran the non-const body (libc++'s __hash_table::__count_unique,
// behind unordered_set::count).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct table
{
  template <class K>
  int find(const K &);
  template <class K>
  int find(const K &) const;
  template <class K>
  int count(const K &k) const;
  template <class K>
  int count_mutable(const K &k);
};
template <class T>
template <class K>
int table<T>::find(const K &)
{
  return 1;
}
template <class T>
template <class K>
int table<T>::find(const K &) const
{
  return 2;
}
template <class T>
template <class K>
int table<T>::count(const K &k) const
{
  return find(k);
}
template <class T>
template <class K>
int table<T>::count_mutable(const K &k)
{
  return find(k);
}
struct plain
{
  template <class K>
  int find(const K &)
  {
    return 1;
  }
  template <class K>
  int find(const K &) const
  {
    return 2;
  }
  int count(int k) const
  {
    return find(k);
  }
  int count_this(int k) const
  {
    return this->find(k);
  }
};
int main()
{
  table<int> t;
  const table<int> &c = t;
  plain p;
  __CPROVER_assert(t.find(1) == 1, "non-const object");
  __CPROVER_assert(c.find(1) == 2, "const object");
  __CPROVER_assert(t.count(1) == 2, "from a const member function");
  __CPROVER_assert(t.count_mutable(1) == 1, "from a non-const one");
  __CPROVER_assert(p.count(1) == 2, "class, implicit object");
  __CPROVER_assert(p.count_this(1) == 2, "class, this->");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
