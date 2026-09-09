// N5008 [temp.type]/1: two template-ids refer to the same class only if
// their template arguments are identical -- so the rendering of an
// argument into an instantiated type's name must be CANONICAL.  A
// template TEMPLATE argument is represented internally as a
// template_parameter_symbol_type whose identifier sometimes carries a
// numeric scope prefix and sometimes does not, depending on the path
// that produced it; rendering it raw gave the same specialization two
// different names, so a lookup of one spelling missed the symbol
// created under the other.  In libc++ 23 that made the base class of
//   __split_buffer<T, A, __split_buffer_pointer_layout>
// unfollowable, hiding its inherited members.
// This test pins the naming: no placeholder may appear in the symbol
// table for a program instantiating a template through a template
// template argument.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class A> struct vlayout;
template <class SB, class T, class A> struct sb_layout
{
  void relocate(T *&b, T *&e, T *&c)
  {
    b = e;
    c = e;
  }
};
template <class T, class A, template <class, class, class> class Layout>
class sbuf : Layout<sbuf<T, A, Layout>, T, A>
{
  template <class, class> friend struct vlayout;
};
template <class T, class A> struct vlayout
{
  using SB = sbuf<T, A, sb_layout>;
  T *begin_ = nullptr;
  T *end_ = nullptr;
  T *cap_ = nullptr;
  unsigned n_ = 0;
  void relocate(SB &buf);
};
template <class T, class A> void vlayout<T, A>::relocate(SB &buf)
{
  buf.relocate(begin_, end_, cap_);
  n_ = 7;
}
int main()
{
  vlayout<int, int> l;
  vlayout<int, int>::SB b;
  l.relocate(b);
  __CPROVER_assert(l.n_ == 7, "TT argument named in a member alias of another template");
  return 0;
}
