extern "C" void __CPROVER_assert(bool, const char *);
template <class T> struct G { T lo; T hi; };
using lreg_t = G<unsigned short>;
typedef G<unsigned int> wreg_t;
template <class T> struct A { T v; };
struct Z { int q; };
using zal_t = Z __attribute__((aligned(16)));
int main()
{
  __CPROVER_assert(sizeof(lreg_t) == 4, "sizeof of an alias to a class template instance");
  __CPROVER_assert(sizeof(wreg_t) == 8, "sizeof of a typedef to a class template instance");
  __CPROVER_assert(alignof(A<double>) == 8 && sizeof(A<char>) == 1, "alignof/sizeof of an instance named for the first time");
  __CPROVER_assert(sizeof(zal_t) == 4, "attributed alias of a plain struct");
  return 0;
}
