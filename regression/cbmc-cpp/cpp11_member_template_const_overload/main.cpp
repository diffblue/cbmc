// N5008 [over.call.func]/3 + [over.ics.rank]/3.2.6: an unqualified
// member call's implied object argument is (*this); a non-const
// enclosing member selects the non-const overload of a const /
// non-const member-template pair.  CBMC's ranking only applied the
// cv-penalty for EXPLICIT objects, so the pair tied ("does not
// uniquely resolve") whenever the return types differ, and the
// CALLER was silently dropped.  Distilled from libc++
// __tree::find/__lower_bound (std::map::find returned havoc; a
// find()==end() comparison on an EMPTY map was falsifiable).
extern "C" void __CPROVER_assert(bool, const char *);
struct tree
{
  template <class K> int lb(K v)
  {
    return 1;
  }
  template <class K> void lb(K v) const
  {
  }
  template <class K> int find(K v)
  {
    return lb(v); // non-const this: must select the non-const overload
  }
};
int main()
{
  tree t;
  __CPROVER_assert(t.find(5) == 1, "non-const member template selected");
  return 0;
}
