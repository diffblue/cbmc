// A member function taking a "const_iterator"-like type, called with an
// "iterator"-like argument, inside an instantiated function template body.
// The iterator -> const_iterator conversion is a user-defined conversion via
// a converting constructor template whose parameter is a class-template-id
// (Iter<Q, C>); Q is deduced from the argument ([temp.deduct.type]/3.3).
//
// This mirrors libstdc++ vector::erase(const_iterator, const_iterator) called
// (in std::erase_if's body) with iterator arguments.  Direct initialization
// `const_iterator c = it;` resolves the conversion correctly, but during the
// member-call overload resolution for erase() inside the template body the
// candidate is rejected before the user-defined conversion is applied, so the
// call is dropped and the container is not modified -- here `n` stays 3 and the
// assertion fails.  (In a non-template / direct call site the same unresolved
// call is silently dropped together with the rest of the full-expression, which
// is why such uses appear to "pass" only vacuously.)
//
// KNOWNBUG: reclassify CORE once the iterator->const_iterator user-defined
// conversion (template converting constructor with a class-template-id
// parameter) is applied during member-call overload resolution.
template <typename P, typename C>
struct Iter
{
  P p;
  Iter() : p(0) {}
  template <typename Q>
  Iter(const Iter<Q, C> &) : p(0)
  {
  }
};
template <typename T>
struct Vec
{
  typedef T *pointer;
  typedef Iter<T *, Vec> iterator;
  typedef Iter<const T *, Vec> const_iterator;
  int n;
  iterator begin() { return iterator{}; }
  iterator end() { return iterator{}; }
  void erase(const_iterator, const_iterator) { n = n - 1; }
};
template <typename T>
void doit(Vec<T> &c)
{
  c.erase(c.begin(), c.end()); // iterator args -> const_iterator params
}
int main()
{
  Vec<int> v;
  v.n = 3;
  doit(v);
  __CPROVER_assert(v.n == 2, "member erase(iterator->const_iterator) in template body");
  return 0;
}
