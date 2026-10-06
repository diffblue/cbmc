// N5008 [expr.prim.req.general]/5, [dcl.fct]/13: a requires-expression
// whose parameter has an incomplete class type by value is not satisfied
// (substituting the type into the parameter-declaration fails)
extern "C" void __CPROVER_assert(bool, const char *);
template <class I>
concept subtractable = requires(I a, I b) { a - b; };
template <class T>
struct wrapper;
template <class T>
int operator-(wrapper<T>, wrapper<T>);
struct incomplete;
struct complete
{
};
template <>
struct wrapper<complete>
{
};
int main()
{
  __CPROVER_assert(
    !subtractable<wrapper<incomplete>>, "parameter of incomplete type");
  __CPROVER_assert(subtractable<wrapper<complete>>, "complete type");
  __CPROVER_assert(!subtractable<wrapper<complete>>, "WRONG (must FAIL)");
}
