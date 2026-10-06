// N5008 [basic.fundamental]/9, [lex.string]/6: char8_t is a distinct type
// whose underlying type is unsigned char; u8 literals have type
// const char8_t[N]
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct kind
{
  static const int value = 0;
};
template <>
struct kind<char8_t>
{
  static const int value = 1;
};
int main()
{
  __CPROVER_assert(
    kind<unsigned char>::value == 0 && kind<char8_t>::value == 1,
    "specialization");
  __CPROVER_assert(!__is_same(char8_t, unsigned char), "__is_same");
  __CPROVER_assert(
    __is_same(decltype(u8"a"), const char8_t(&)[2]), "u8 string literal");
  __CPROVER_assert(kind<char8_t>::value == 0, "WRONG (must FAIL)");
}
