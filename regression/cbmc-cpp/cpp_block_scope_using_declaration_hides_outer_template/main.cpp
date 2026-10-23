extern "C" void __CPROVER_assert(bool, const char *);
namespace s
{
template <typename T>
struct is_mi
{
  enum
  {
    value = 0
  };
};
namespace r
{
namespace d
{
template <typename T>
int is_mi(T *)
{
  return 1;
}
} // namespace d
// [basic.lookup.general]/1, [basic.lookup.unqual]/1-2: the search for is_mi
// stops at the block scope, where the using-declaration introduced d::is_mi
// ([namespace.udecl]/1); the class template s::is_mi is hidden
// (libstdc++'s ranges::__copy_or_move: `using __detail::__is_move_iterator;'
// next to std::__is_move_iterator)
int f(int *p)
{
  using d::is_mi;
  return is_mi<int>(p);
}
} // namespace r
} // namespace s
int main()
{
  int i = 0;
  __CPROVER_assert(s::r::f(&i) == 1, "block-scope using-declaration");
  __CPROVER_assert(s::r::f(&i) != 1, "WRONG (must FAIL)");
}
