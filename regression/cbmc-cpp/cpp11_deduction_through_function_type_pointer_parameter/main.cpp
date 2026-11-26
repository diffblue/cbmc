// N5008 [temp.deduct.type]/8: T is deduced from a function type's parameter
// of the form T *, T & or const T & -- here inside a class template
// argument, fn<void(T *)> against fn<void(ex *)>.  The parameter types of
// such a function type are still in front-end form on both sides, and the
// pointer or reference declarator was not matched, so no T was deduced:
// "found no match for symbol 'visit_pre_template'" (CBMC's own
// exprt::visit_pre, `visit_pre_template(std::function<void(T &)>, T *)',
// dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
template <class>
struct fn
{
};
struct ex
{
  int v = 3;
};
template <typename T>
int by_pointer(fn<void(T *)>, T *p)
{
  return p->v;
}
template <typename T>
int by_reference(fn<void(T &)>)
{
  return sizeof(T) == sizeof(ex) ? 1 : 0;
}
template <typename T>
int by_const_reference(fn<void(const T &)>)
{
  return sizeof(T) == sizeof(int) ? 1 : 0;
}
int main()
{
  ex e;
  fn<void(ex *)> f1;
  fn<void(ex &)> f2;
  fn<void(const int &)> f3;
  __CPROVER_assert(by_pointer(f1, &e) == 3, "T * deduced");
  __CPROVER_assert(by_reference(f2) == 1, "T & deduced");
  __CPROVER_assert(by_const_reference(f3) == 1, "const T & deduced");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
