// N5008 [class.copy.assign]/12, [class.copy.ctor]/14: the implicitly-
// defined copy/move assignment and constructor identify each base
// subobject by TYPE.  With two bases from the SAME class template
// (libstdc++'s _Hashtable_base : _Hashtable_ebo_helper<1, H1>,
// _Hashtable_ebo_helper<0, H2> shape), synthesizing the copy from the
// base's unqualified NAME made resolution ambiguous: "symbol
// '_Hashtable_ebo_helper' does not uniquely resolve".
// Found dog-fooding src/util/{symbol_table,interval,expr_initializer}.cpp.
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

template <int N, typename T>
struct ebo_helper
{
  T value;
};

struct hasher
{
  int h;
};

struct equal
{
  int e;
};

struct table : ebo_helper<1, hasher>, ebo_helper<0, equal>
{
};

int main()
{
  table a;
  static_cast<ebo_helper<1, hasher> &>(a).value.h = 7;
  static_cast<ebo_helper<0, equal> &>(a).value.e = 9;

  table b;
  b = a; // implicit copy assignment: one base per TYPE

  __CPROVER_assert(
    static_cast<ebo_helper<1, hasher> &>(b).value.h == 7,
    "first base copied");
  __CPROVER_assert(
    static_cast<ebo_helper<0, equal> &>(b).value.e == 9,
    "second base copied");

  table c(a); // implicit copy constructor, POD bases
  __CPROVER_assert(
    static_cast<ebo_helper<0, equal> &>(c).value.e == 9,
    "copy ctor base copied");
  return 0;
}
