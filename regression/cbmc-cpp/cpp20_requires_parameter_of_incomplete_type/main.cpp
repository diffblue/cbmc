// N5008 [expr.call]/7, [expr.prim.req.general]/5: a requirement calling a
// function with a by-value parameter of an incomplete class type is
// ill-formed, so the requirement is not satisfied
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
