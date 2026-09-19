// N5008 [lex.string]/6: an ordinary string literal has type "array of n
// const char" and is an lvalue ([expr.prim.literal]/1).  The C front-end
// types it `char[n]' (C's rule), which in C++ mis-ranked overload
// candidates: `std::string s("...")' selected the string_view constructor
// template (an identity binding of `const _Tp &' to `char[n]') over the
// non-template `basic_string(const char *)' (a qualification conversion on
// top of the array-to-pointer conversion), and every INVARIANT-style
// `f(__FILE__, __func__, ...)' call reported "symbol 'basic_string' does
// not uniquely resolve".
extern "C" void __CPROVER_assert(bool, const char *);
#include <string>
#include <type_traits>

struct X
{
  explicit X(std::string m) : message(m)
  {
  }
  std::string message;
};

char *legacy = "legacy"; // C++03 [conv.array]/2, dropped in C++11; GCC and
                         // clang accept it with a warning, so do we
void take_char_ptr(char *)
{
}
template <class T>
int which(T)
{
  return 1;
}
int which(const char *)
{
  return 2;
}
int which2(char *)
{
  return 1;
}
int which2(const char *)
{
  return 2;
}
const char arr[4] = "abc";
typedef const char T4[4];

int main()
{
  static_assert(
    std::is_same<decltype("abc"), const char(&)[4]>::value,
    "[lex.string]/6, [dcl.type.decltype]/1.5: const char (&)[4]");
  static_assert(
    sizeof(__func__) == 5,
    "[dcl.fct.def.general]/8: static const char __func__[] = \"main\"");
  static_assert(
    std::is_same<std::remove_reference<decltype("abc")>::type, T4>::value,
    "array types agree whatever way the bound was spelled");
  static_assert(
    std::is_same<decltype(arr), const char[4]>::value, "declared array");
  static_assert(
    sizeof(int &) == sizeof(int), "[expr.sizeof]/2: referenced type");
  static_assert(sizeof(decltype("abc")) == 4, "sizeof of a reference to array");
  __CPROVER_assert(sizeof("abc") == 4, "sizeof literal");
  X x("nullary expression must not have operands");
  __CPROVER_assert(
    x.message.size() == 41,
    "explicit ctor with a std::string parameter from a literal");
  std::string s("hello world, a longer literal here...");
  __CPROVER_assert(s.size() == 37, "direct-init from a literal");
  std::string f(__func__);
  __CPROVER_assert(f == "main", "std::string from __func__");
  take_char_ptr("abc");
  __CPROVER_assert(legacy[0] == 'l', "legacy char * from a literal");
  __CPROVER_assert(which("abc") == 2, "non-template preferred on a tie");
  __CPROVER_assert(
    which2("abc") == 2, "const char * beats the deprecated char * conversion");
  return 0;
}
