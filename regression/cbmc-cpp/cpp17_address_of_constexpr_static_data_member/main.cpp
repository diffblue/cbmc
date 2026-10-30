extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct unique_typeinfo
{
  static constexpr int id = 0;
};
// the definition of the static data member ([class.static.data]/4)
template <class T>
constexpr int unique_typeinfo<T>::id;
// libc++'s any: a type's identity is the address of its static member
template <class T>
constexpr const void *fallback_typeid()
{
  return &unique_typeinfo<T>::id;
}
int main()
{
  // [basic.compound]/3, [expr.unary.op]/3: distinct objects have distinct
  // addresses
  __CPROVER_assert(
    fallback_typeid<int>() != fallback_typeid<char>(), "distinct identities");
  __CPROVER_assert(
    fallback_typeid<int>() == fallback_typeid<int>(), "stable identity");
  __CPROVER_assert(
    fallback_typeid<int>() == fallback_typeid<char>(), "WRONG (must FAIL)");
}
