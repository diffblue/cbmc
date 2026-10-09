// N5008 [temp.inst]/2: the implicit instantiation of a class template
// specialization instantiates the *declarations* of its member function
// templates, but NOT their definitions, and a member function template's
// signature remains dependent on its own template parameters -- it is not
// instantiated until the specialization is used (odr-used).
//
// std::unique_ptr<T> declares a =delete'd constructor template of the shape
//   template<class _Del = deleter_type,
//            class _DelUnref = std::remove_reference_t<_Del>>
//   unique_ptr(pointer,
//              std::enable_if_t<std::is_lvalue_reference_v<_Del>,
//                               _DelUnref&&>) = delete;   // unique_ptr.h
// When the enclosing class UI (which has a std::unique_ptr<C> member and a
// defaulted move constructor, forcing full elaboration of unique_ptr<C>) is
// processed, CBMC concretizes this member constructor template -- substituting
// the default _Del = deleter_type = std::default_delete<C> and evaluating the
// parameter type.  is_lvalue_reference_v<default_delete<C>> is false, so it
// demands std::enable_if_t<false>::type, which does not exist, and CBMC reports
//   instantiating 'std::__enable_if_t' with <FALSE, struct default_delete &&>
// as a hard error (and then a malformed model aborts symbolic execution).
//
// A conforming implementation leaves this member constructor template
// uninstantiated (its signature dependent on _Del), so the =delete'd overload
// never contributes an ill-formed enable_if_t<false>.  g++ and clang++ accept
// this program.
//
// FIXED: the hard error is gone (the =delete constructor template is no
// longer concretized), and the subsequent value bugs were fixed by modelling
// C++17 inheriting constructors ([class.inhctor.init]), xvalue base
// initialization in defaulted move constructors ([class.copy.ctor]/15), and
// memberwise elaboration of defaulted copy/move assignment operators
// ([class.copy.assign]/12).  assertion.2 must FAIL (non-vacuity).

#include <memory>

extern "C" void __CPROVER_assert(int, const char *);

struct C
{
  int v;
  explicit C(int x) : v(x)
  {
  }
};

struct UI
{
  std::unique_ptr<C> p;
  UI()
  {
  }
  UI(UI &&) = default;
  ~UI();
};

UI::~UI()
{
}

int main()
{
  UI u;
  u.p = std::unique_ptr<C>(new C(5));
  __CPROVER_assert(u.p->v == 5, "unique_ptr member holds its value");
  __CPROVER_assert(u.p->v != 5, "WRONG must FAIL");
  return 0;
}
