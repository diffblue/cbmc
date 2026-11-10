// N5008 [meta.unary.prop]/5: a class whose only non-static data member is
// an empty [[no_unique_address]] member (a subobject of zero size,
// [intro.object]/8) is empty; as a base it has zero size and, as GCC and
// Clang (Itanium C++ ABI 2.4 II.3) lay it out, lies at offset 0.  A
// non-empty base with such a member keeps the member's offset in the base.
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
};
struct H
{
  [[no_unique_address]] E e;
};
struct I
{
  int i;
};
struct T : I, H
{
};
struct K
{
  int k;
  [[no_unique_address]] E e;
};
struct U : I, K
{
};
static_assert(std::is_empty<H>::value, "is_empty");

int main()
{
  T t;
  t.i = 3;
  H &h = t;
  E &e = h.e;
  e = E{};
  E copy(h.e);
  (void)copy;
  __CPROVER_assert(sizeof(T) == sizeof(int), "empty base");
  __CPROVER_assert(
    (char *)&h == (char *)&t && (char *)&e == (char *)&t, "at offset 0");
  __CPROVER_assert(t.i == 3, "storing the member writes nothing");
  U u;
  __CPROVER_assert(
    sizeof(U) == 2 * sizeof(int) && (char *)&u.e - (char *)&u == sizeof(int),
    "member of a non-empty base");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
