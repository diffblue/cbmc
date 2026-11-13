// N5008 [expr.cond]/4, [dcl.type.decltype]: cv-combination and value
// category of the conditional operator over glvalues.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
T &&declval();

struct W
{
  int v;
};

int main()
{
  static_assert(
    __is_same(
      decltype(false ? declval<W &>() : declval<const W &>()), const W &),
    "lvalue W, lvalue const W -> lvalue const W");
  static_assert(
    __is_same(
      decltype(false ? declval<const W &>() : declval<W &>()), const W &),
    "order does not matter");
  static_assert(
    __is_same(
      decltype(false ? declval<int &>() : declval<const int &>()), const int &),
    "scalar lvalues");
  static_assert(
    __is_same(decltype(false ? declval<W &&>() : declval<W &&>()), W &&),
    "two xvalues -> xvalue");
  static_assert(
    __is_same(decltype(false ? declval<W &>() : declval<W &&>()), W),
    "lvalue and xvalue -> prvalue");
  static_assert(
    __is_same(
      decltype(false ? declval<const W &>() : declval<W &&>()), const W),
    "class prvalue keeps the combined cv");
  static_assert(
    __is_same(
      decltype(false ? declval<const int &>() : declval<int &&>()), int),
    "non-class prvalue is cv-unqualified");
  static_assert(
    __is_same(decltype(false ? declval<int &>() : declval<int &&>()), int),
    "int lvalue and xvalue -> int");

  W w{1};
  const W cw{2};
  const W &r = true ? w : cw;
  __CPROVER_assert(r.v == 1, "the lvalue result refers to the chosen operand");
  return 0;
}
