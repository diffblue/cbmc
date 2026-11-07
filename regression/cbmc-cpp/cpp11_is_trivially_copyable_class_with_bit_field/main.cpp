extern "C" void __CPROVER_assert(bool, const char *);
enum class alignment : unsigned char
{
  left,
  right
};
struct std_flags
{
  alignment a : 3;
  bool sign : 1;
};
template <class C>
struct code_point
{
  C data[4 / sizeof(C)];
};
// libc++'s __parsed_specifications: an anonymous union with a bit-field
// and class-type members, plain members, a class-template member
template <class C>
struct parsed
{
  union
  {
    alignment al : 3;
    std_flags st;
  };
  int width;
  int precision;
  code_point<C> fill;
  constexpr bool has_width() const
  {
    return width > 0;
  }
};
// [class.prop]/1, [basic.types.general]/9: no non-trivial copy/move
// constructor, assignment or destructor anywhere, so trivially copyable
struct bits
{
  int a : 3;
};
static_assert(__is_trivially_copyable(bits), "a bit-field alone");
static_assert(sizeof(parsed<char>) == 16, "size");
static_assert(__is_trivially_copyable(parsed<char>), "trivially copyable");
static_assert(__is_trivially_copyable(parsed<wchar_t>), "wchar_t too");
int main()
{
  bool b = __is_trivially_copyable(parsed<char>);
  __CPROVER_assert(b, "trivially copyable at run time");
  __CPROVER_assert(!b, "WRONG (must FAIL)");
}
