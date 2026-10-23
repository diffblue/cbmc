// N5008 [dcl.enum]/2, [temp.arg.nontype]: an enumeration with underlying
// type bool is a valid non-type template parameter type (the shape of
// std::ranges::subrange_kind in subrange's default template argument)
extern "C" void __CPROVER_assert(bool, const char *);
enum class kind : bool
{
  unsized,
  sized
};
template <class T, kind K = kind::sized>
struct sub
{
  T v;
  static constexpr bool is_sized = K == kind::sized;
};
int main()
{
  sub<int> s{3};
  sub<int, kind::unsized> u{4};
  __CPROVER_assert(s.v == 3 && sub<int>::is_sized, "default argument");
  __CPROVER_assert(!sub<int, kind::unsized>::is_sized && u.v == 4, "explicit");
  __CPROVER_assert(!sub<int>::is_sized, "WRONG (must FAIL)");
  return 0;
}
