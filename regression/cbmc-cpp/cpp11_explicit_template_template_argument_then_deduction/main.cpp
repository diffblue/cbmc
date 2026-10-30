extern "C" void __CPROVER_assert(bool, const char *);
template <template <class...> class T, class... A>
int impl(const T<A...> &)
{
  return sizeof...(A);
}
template <class D>
struct interface
{
};
template <class R>
struct view : interface<view<R>>
{
};
template <class X, class Y>
struct two
{
};
// N5008 [temp.arg.explicit]/2, [temp.deduct.call]/4.3: the template template
// parameter T is given explicitly; A... is deduced from the argument, or from
// its base class that is a specialization of T (the MSVC STL's
// _Derived_from_specialization_impl<view_interface>, behind ranges::view)
int main()
{
  view<int> v;
  two<int, char> t;
  __CPROVER_assert(
    impl<interface>(v) == 1 && impl<two>(t) == 2,
    "remaining arguments deduced");
  __CPROVER_assert(impl<two>(t) == 1, "WRONG (must FAIL)");
  return 0;
}
