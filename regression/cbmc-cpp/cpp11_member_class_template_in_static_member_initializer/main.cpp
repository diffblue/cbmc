extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
// libc++'s __libcpp_datasizeof<_Tp> (when __datasizeof is unavailable): a
// static data member's in-class initializer instantiates a member class
// template of the enclosing class template
template <class T>
struct datasizeof
{
  template <class = char>
  struct first_padding_byte
  {
    T v;
    char byte;
  };
  static const size_t value = __builtin_offsetof(first_padding_byte<>, byte);
  static constexpr size_t size()
  {
    return sizeof(first_padding_byte<>);
  }
};
struct S
{
  int i;
  char c;
};
static_assert(datasizeof<char>::value == 1, "char");
static_assert(datasizeof<int>::value == 4, "int");
static_assert(datasizeof<S>::value == 8, "S: its size, 4 + 1 + 3 padding");
static_assert(
  datasizeof<long>::size() == 16,
  "the member instance is complete");
int main()
{
  datasizeof<int>::first_padding_byte<> f{1, 'x'};
  __CPROVER_assert(f.v == 1 && f.byte == 'x', "members of the member instance");
  __CPROVER_assert(datasizeof<short>::value == 2, "short");
  __CPROVER_assert(datasizeof<short>::value == 4, "WRONG (must FAIL)");
}
