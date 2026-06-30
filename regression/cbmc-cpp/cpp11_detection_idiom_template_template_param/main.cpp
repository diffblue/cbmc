// N5008 [temp.class.spec.match] + [temp.alias]/2 + [temp.deduct]: a class
// template partial specialization is selected when its argument list, after
// deduction and substitution, matches the specialization arguments and every
// substituted argument is valid.  The detection idiom relies on this:
//
//   template <template <typename...> class Op, typename Arg, typename = void>
//   struct has { static constexpr bool value = false; };
//   template <template <typename...> class Op, typename Arg>
//   struct has<Op, Arg, void_t<Op<Arg>>> { static constexpr bool value = true; };
//
// For has<foo_t, WithFoo> (where foo_t<T> = typename T::foo and WithFoo has a
// member foo), Op<Arg> = foo_t<WithFoo> = int is valid, so void_t<Op<Arg>> is
// void, the partial specialization matches, and value is TRUE.  g++ and clang++
// agree (WithFoo=1, NoFoo=0).
//
// This was a KNOWN BUG and is now fixed.  CBMC reported has<foo_t, WithFoo>::
// value as FALSE: when verifying the partial specialization, typecheck_template_
// args correctly deduced Op -> foo_t into the template_map, but resolving the
// written template-template-parameter argument relied on
// cpp_scopes.id_map.find(deduced-template-id), which can fail (the template's
// scope-id key differs from its symbol identifier); the empty result then fell
// through to a global-name fallback that re-selected the template-template-
// PARAMETER itself, leaving the argument unsubstituted so the specialization did
// not match.  Fixed by wiring the argument directly from its deduced
// template_map binding ([temp.arg.template], [temp.class.spec.match]).  The
// equivalent detection written with a direct member access
// ( void_t<typename T::foo> ) already worked; this is the template-template-
// parameter analogue (the shape of libstdc++ std::__detected_or).
//
// Non-vacuous: assertion 3 ("WRONG") must FAIL.  Flip to CORE once the partial
// specialization is matched for the template-template-parameter case.

extern "C" void __CPROVER_assert(int, const char *);

template <typename...>
using void_t = void;

template <typename T>
using foo_t = typename T::foo;

template <template <typename...> class Op, typename Arg, typename = void>
struct has
{
  static constexpr bool value = false;
};

template <template <typename...> class Op, typename Arg>
struct has<Op, Arg, void_t<Op<Arg>>>
{
  static constexpr bool value = true;
};

struct WithFoo
{
  using foo = int;
};

struct NoFoo
{
};

int main()
{
  __CPROVER_assert(has<foo_t, WithFoo>::value, "Op<WithFoo> valid -> detected");
  __CPROVER_assert(!has<foo_t, NoFoo>::value, "Op<NoFoo> invalid -> not detected");
  __CPROVER_assert(!has<foo_t, WithFoo>::value, "WRONG must FAIL");
  return 0;
}
