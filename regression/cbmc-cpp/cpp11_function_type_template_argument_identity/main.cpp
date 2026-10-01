extern "C" void __CPROVER_assert(bool, const char *);
void cb(int k)
{
}
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
// [temp.type]/1, [dcl.fct]/5: decltype(cb) and the type-id void(int) denote
// the same function type, so same<...> is its partial specialization
int main()
{
  __CPROVER_assert(same<decltype(cb), void(int)>::value, "function type");
  __CPROVER_assert(!same<decltype(cb), void(int)>::value, "WRONG (must FAIL)");
}
