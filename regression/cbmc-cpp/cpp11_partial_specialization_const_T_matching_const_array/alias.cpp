extern "C" void __CPROVER_assert(bool, const char *);
template <class A, class B>
struct same
{
  static const bool value = false;
};
template <class A>
struct same<A, A>
{
  static const bool value = true;
};
template <class T>
struct is_const
{
  static const bool value = false;
};
template <class T>
struct is_const<const T>
{
  static const bool value = true;
};
template <class T>
struct element;
template <class T, unsigned long N>
struct element<T[N]>
{
  typedef T type;
};
// [basic.type.qualifier]/3 and Note 2: cv-qualifiers applied to an array
// type attach to the element type, whether the array type is named by a
// typedef or a template parameter (libstdc++'s basic_format_string,
// `convertible_to<const _Tp &, basic_string_view<_CharT>>' with
// _Tp = char[3])
typedef char A3[3];
template <class T>
using cref = const T &;
const A3 a = "ab";
cref<char[3]> r = "cd";
int main()
{
  __CPROVER_assert(same<cref<char[3]>, const char(&)[3]>::value, "alias");
  __CPROVER_assert(
    is_const<element<decltype(a)>::type>::value, "typedef element");
  __CPROVER_assert(r[1] == 'd', "reference to array of const char");
  __CPROVER_assert(r[1] != 'd', "WRONG (must FAIL)");
}
