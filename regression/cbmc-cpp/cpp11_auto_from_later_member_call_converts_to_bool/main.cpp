// N5008 [temp.inst]/2: a class template specialization is implicitly
// instantiated when completeness affects the semantics of the program;
// [conv.general]/4, [class.conv.fct]: the contextual conversion of a class
// object to bool uses its conversion function, so the class must be
// complete.  The type of `auto number' deduced from a call to a member
// function declared LATER in the class was a still-unelaborated
// specialization: `if(number)' failed with "invalid implicit conversion
// from 'struct nil' to bool" (CBMC's own inv_object_storet::get with
// std::optional, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct opt
{
  bool has;
  T v;
  explicit operator bool() const
  {
    return has;
  }
};
struct store
{
  int k;
  bool get(int s)
  {
    auto number = lookup(s);
    if(number)
      return true;
    return false;
  }
  opt<unsigned> lookup(int s) const
  {
    return opt<unsigned>{s == k, 7u};
  }
};
int main()
{
  store st{1};
  __CPROVER_assert(st.get(1), "found");
  __CPROVER_assert(!st.get(2), "missing");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
