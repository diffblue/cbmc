// N5008 [expr.prim.req]: a requires-expression in a variable template.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
constexpr bool has_size = requires(T t) { t.size(); };
struct S
{
  int size()
  {
    return 0;
  }
};
int main()
{
  __CPROVER_assert(has_size<S> && !has_size<int>, "requires-expression");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
