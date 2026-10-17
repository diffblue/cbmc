// Regression for [over.match.copy]/1 + [over.ics.user] + [temp.deduct]:
// a user-defined conversion sequence may select a *function-template*
// converting constructor.  Such a constructor's instantiation is a
// legitimate participant in copy-initialization.
//
// CBMC's `user_defined_conversion_sequence` has a fallback path for
// classes whose only converting constructor is a template
// (`has_template_constructor`).  After `new_temporary` instantiates
// the template constructor, the result was accepted only if the
// selected constructor symbol carried `ID_specialization_of` — the
// tag CBMC puts on CLASS template specializations.  But a member
// converting-constructor *function* template (e.g.,
// `optional(_Up &&)`) becomes a FUNCTION template instantiation when
// `_Up` is deduced, and those are tagged with `#fn_template_args`,
// not `ID_specialization_of`.  The check therefore wrongly rejected
// the perfectly valid instantiation and the whole conversion failed
// with
//
//   invalid implicit conversion from 'T' to 'struct <class>'
//
// for any copy-initialization (notably `return v;`) where the target
// is a class whose viable converting constructor is a template.
//
// The fix accepts the instantiated constructor when EITHER tag is
// present (and it is non-explicit, per [over.match.copy]/1).
//
// This pattern is the shape of `std::optional<T>`'s converting
// constructor `optional(_Up&&)`; CBMC's own source returns `T` into
// `std::optional<T>` in several places.  The synthetic container here
// exercises the same typecheck path (member function-template
// converting constructor + forwarding reference + SFINAE guard)
// without the deeper libstdc++ `_Optional_base` payload machinery.

#include <type_traits>

template <typename T>
struct myopt
{
  bool engaged;
  T value;

  myopt() : engaged(false), value()
  {
  }

  // Function-template converting constructor with a forwarding
  // reference and a SFINAE guard, mirroring libstdc++
  // `optional(_Up&&)`.  Its instantiation is tagged with
  // `#fn_template_args`, not `ID_specialization_of`.
  template <
    typename U = T,
    std::enable_if_t<
      std::is_constructible_v<T, U> && std::is_convertible_v<U, T>,
      bool> = true>
  myopt(U &&v) : engaged(true), value(static_cast<T>(v))
  {
  }
};

// `return x;` copy-initializes the `myopt<int>` return value from
// `int` via the converting constructor template.  Pre-fix: rejected.
myopt<int> get(int x)
{
  return x;
}

int main()
{
  auto r = get(5);
  return r.engaged ? 0 : 1;
}
