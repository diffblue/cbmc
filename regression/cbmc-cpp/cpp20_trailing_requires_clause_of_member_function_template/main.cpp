extern "C" void __CPROVER_assert(bool, const char *);
template <class R>
class ref
{
  R *r;
  static void bind(R &);
  static void bind(R &&) = delete;

public:
  // N5008 [temp.constr.decl]/3, [temp.constr.atomic]/1: the trailing
  // requires-clause of a member function template is checked with the
  // template's own parameter O bound to the deduced argument (the MSVC
  // STL's ranges::ref_view constructor)
  template <class O>
  ref(O &&o) requires requires
  {
    bind(static_cast<O &&>(o));
  }
      : r{&static_cast<R &>(o)}
      {
      }
      template <class O>
      static int size(O) requires requires
      {
        sizeof(O);
      }
      {
        return sizeof(O);
      }
      R &base() const
      {
        return *r;
      }
};
int main()
{
      int a[3] = {1, 2, 3};
      ref<int[3]> v(a);
      __CPROVER_assert(
        v.base()[2] == 3 && ref<int>::size('c') == 1,
        "constrained members viable");
      __CPROVER_assert(v.base()[2] == 2, "WRONG (must FAIL)");
      return 0;
}
