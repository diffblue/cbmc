// N5008 [basic.scope.class]: names declared earlier in a class are in scope
// for subsequent member declarations, so the in-class initializer of a
// static data member must resolve class-local typedefs and members declared
// before it.  (Note: such initializers are NOT among the complete-class
// contexts of [class.mem.general]/9, so LATER-declared siblings need not be
// visible -- g++/clang++ reject that.)
//
// Minimal shape distilled from the __is_swappable-style probe
// (cpp11_is_swappable_unevaluated): cbmc used to type-check the initializer
// in a state where even earlier-declared class-local typedefs did not
// resolve, swallow the failure, and leave a raw cpp_name that read as nondet
// downstream.
extern "C" void __CPROVER_assert(int, const char *);

struct true_type
{
  static const bool value = true;
};

struct probe
{
  static true_type test(int);
  template <typename U>
  static true_type ttest(int);
};

// unqualified read through a class-local typedef
struct wrap1
{
  typedef true_type type;
  static const bool value = type::value;
};

// qualified read through a class-local typedef
struct wrap2
{
  typedef true_type type;
  static const bool value = wrap2::type::value;
};

// typedef of a decltype over a declared-only (member) function call
struct wrap3
{
  typedef decltype(probe::test(0)) type;
  static const bool value = type::value;
};

// typedef of a decltype over a member function TEMPLATE call
struct wrap4
{
  typedef decltype(probe::ttest<int>(0)) type;
  static const bool value = type::value;
};

int main()
{
  __CPROVER_assert(wrap1::value, "unqualified typedef read");
  __CPROVER_assert(wrap2::value, "qualified typedef read");
  __CPROVER_assert(wrap3::value, "decltype typedef read");
  __CPROVER_assert(wrap4::value, "member template decltype typedef read");
  return 0;
}
