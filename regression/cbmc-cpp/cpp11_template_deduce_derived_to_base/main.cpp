// Per [temp.deduct.call]/4.3 (C++11+):
//   "If P is a class and P has the form simple-template-id, then the
//    transformed A can be a derived class of the deduced A.  [...]
//    Likewise, if P is a pointer to a class of the form
//    simple-template-id, the type of the pointee of the transformed
//    A can be a derived class of the pointee type of the deduced A."
//
// Concretely: a function template
//     template <class T> void f(Base<T> const volatile* p);
// called with an argument of type `Derived<bool> const volatile*`
// where `template<class U> struct Derived : Base<U> { ... }` must
// deduce `T = bool` via the derived-to-base rule.
//
// Before the fix, CBMC's `guess_template_args` in
// `cpp_typecheck_resolve.cpp` gave up as soon as the template name
// in P (`Base`) did not match the source template of A (`Derived`).
// The fix adds a walk of A's base-class list and retries deduction
// against the first base that is an instantiation of P.
//
// This is the macOS libc++ `__cxx_atomic_load` failure pattern
// reduced to essentials: `__cxx_atomic_impl<_Tp>` derives from
// `__cxx_atomic_base_impl<_Tp>`; `__cxx_atomic_load` takes
// `__cxx_atomic_base_impl<_Tp> const volatile*`; the call
// `__cxx_atomic_load(&__a_, __m)` (with `__a_` of type
// `__cxx_atomic_impl<bool>`) requires derived-to-base deduction to
// find `_Tp = bool`.

template <class _Tp>
struct base_impl
{
  _Tp value;
};

template <class _Tp, class _Base = base_impl<_Tp>>
struct derived_impl : public _Base
{
};

enum mem_order
{
  mo_seq
};

template <class _Tp>
_Tp load_base(base_impl<_Tp> const volatile *a, mem_order m)
{
  (void)m;
  return a->value;
}

struct flag
{
  derived_impl<bool> a_;

  bool test(mem_order m = mo_seq) const volatile noexcept
  {
    // &a_ has type derived_impl<bool> const volatile*.
    // Per [temp.deduct.call]/4.3, deduction for
    //     load_base<_Tp>(base_impl<_Tp> const volatile*, mem_order)
    // must try derived_impl<bool>'s base class base_impl<bool> and
    // deduce _Tp = bool.
    return bool(true) == load_base(&a_, m);
  }
};

int main()
{
  flag f;
  f.a_.value = true;
  __CPROVER_assert(
    f.test(), "derived-to-base template argument deduction for pointers");
  return 0;
}
