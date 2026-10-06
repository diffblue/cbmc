// N5008 [expr.const]/22, [temp.inst]/8, [expr.prim.req.general]/2: a
// constexpr function template named in a requirement is neither odr-used
// nor needed for constant evaluation, so its definition is not
// instantiated (here it would be ill-formed: `w.value' of an incomplete
// class)
extern "C" void __CPROVER_assert(bool, const char *);
template <class I>
concept subtractable = requires(I a, I b) { a - b; };
template <class T>
struct wrapper;
template <class T>
constexpr int operator-(const wrapper<T> &w, const wrapper<T> &)
{
  return w.value;
}
struct incomplete;
constexpr bool checked = subtractable<wrapper<incomplete>>;
template <class T>
struct wrapper
{
  T value;
};
int main()
{
  __CPROVER_assert(checked, "requirement satisfied");
  wrapper<int> x{7}, y{1};
  __CPROVER_assert(x - y == 7, "instantiated when used");
  __CPROVER_assert(x - y == 6, "WRONG (must FAIL)");
}
