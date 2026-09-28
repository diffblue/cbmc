extern "C" void __CPROVER_assert(bool, const char *);
// Clang builtins used by libc++ 23's numeric_limits:
// __make_unsigned(T) is the type trait behind std::make_unsigned_t,
// __builtin_popcountg(x) counts the set bits of an unsigned integer of any
// width
template <class T>
using make_unsigned_t = __make_unsigned(T);
template <class T>
struct limits
{
  static constexpr int digits =
    __builtin_popcountg(static_cast<make_unsigned_t<T>>(~make_unsigned_t<T>()));
};
static_assert(limits<int>::digits == 32, "popcountg of an unsigned int");
static_assert(limits<long>::digits == 64, "popcountg of an unsigned long");
int main()
{
  __CPROVER_assert(limits<char>::digits == 8, "char");
  __CPROVER_assert(limits<short>::digits == 16, "short");
  __CPROVER_assert(limits<short>::digits == 15, "WRONG (must FAIL)");
}
