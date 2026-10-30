// N5008 [expr.call]/1: `(f)(a, b)' calls f with the two arguments a and b;
// the parentheses around the function name suppress macro expansion (the
// MSVC STL's `(::std:: max)(alignof(_Ty), 16ull)' in _New_alignof), and the
// comma separates arguments, it is not a comma operator ([expr.comma]/2).
extern "C" void __CPROVER_assert(bool, const char *);

namespace lib
{
template <class T>
constexpr const T &max(const T &a, const T &b)
{
  return a < b ? b : a;
}

template <class T>
constexpr unsigned long new_alignof =
  (::lib::max)(alignof(T), static_cast<decltype(alignof(T))>(16));

template <class T>
unsigned long allocation_alignment()
{
  return new_alignof<T>;
}
} // namespace lib

struct alignas(32) wide
{
  char c;
};

int main()
{
  __CPROVER_assert(lib::allocation_alignment<char>() == 16, "at least 16");
  __CPROVER_assert(lib::allocation_alignment<wide>() == 32, "the type's");
  __CPROVER_assert(lib::new_alignof<char> == 15, "WRONG (must FAIL)");
  return 0;
}
