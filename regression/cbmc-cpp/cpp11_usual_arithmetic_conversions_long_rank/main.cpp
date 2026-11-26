// N5008 [conv.rank]/1, [expr.arith.conv]/1.5: long and long long rank above
// int and long even where they have the same width (32-bit long on i386
// and Windows, 64-bit long long on LP64).  An operand of lesser rank is
// converted; if the signed type cannot represent all values of the other,
// unsigned type, both convert to the unsigned type of the signed one.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
struct same
{
  static const bool value = false;
};
template <class T>
struct same<T, T>
{
  static const bool value = true;
};
template <bool B, class T, class F>
struct cond
{
  typedef T type;
};
template <class T, class F>
struct cond<false, T, F>
{
  typedef F type;
};
bool b;
long l;
long long ll;
static_assert(same<decltype(1 + l), long>::value, "int + long");
static_assert(same<decltype(b ? 1 : l), long>::value, "int : long");
static_assert(same<decltype(1l + ll), long long>::value, "long + long long");
typedef cond<(sizeof(long) > sizeof(int)), long, unsigned long>::type ul_t;
static_assert(same<decltype(1u + l), ul_t>::value, "unsigned + long");
static_assert(same<decltype(b ? 1u : l), ul_t>::value, "unsigned : long");
typedef cond<
  (sizeof(long long) > sizeof(long)),
  long long,
  unsigned long long>::type ull_t;
static_assert(same<decltype(1ul + ll), ull_t>::value, "ul + long long");
int main()
{
  __CPROVER_assert(same<decltype(1 + l), long>::value, "int + long is long");
  __CPROVER_assert(same<decltype(1 + l), int>::value, "WRONG (must FAIL)");
  return 0;
}
