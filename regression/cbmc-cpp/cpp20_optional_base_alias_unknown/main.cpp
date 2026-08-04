// Minimal faithful shape of libc++ <optional>'s enable-if constructor
// pair (round-11 rewrite of the earlier degenerate reduction):
//   * TWO member constructor templates with the SAME function signature
//     `(_Up&&)`, differing only in their second template parameter (a
//     deduced-class-type NTTP `enable_if_t` vs a dependent
//     `enable_if_t<_Up::__enable_explicit>`) -- N5008 [temp.inst]/2:
//     instantiating optional<int> instantiates only their DECLARATIONS,
//     in which `_Up`-dependent constructs stay dependent, so `_Up` must
//     remain resolvable as a template parameter.
//   * the member alias `__base` for the dependent base (whose bool NTTP
//     default evaluates builtin traits over a builtin alias type,
//     [temp.local] injected-class-name without an argument list) used in
//     a ctor mem-initializer.
// clang builtins (__add_rvalue_reference et al.) => CLANG mode
// (--stdlib libc++); clang++ accepts and runs this clean.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool> struct enable_if;
template <bool _Bp> using enable_if_t = enable_if<_Bp>;
template <int __v> struct integral_constant {
  static const int value = __v;
};
template <class _Tp>
using __add_rvalue_reference_t = __add_rvalue_reference(_Tp);
template <bool = integral_constant<__is_trivially_constructible(
              __add_rvalue_reference_t<int>)>::value>
struct __optional_move_assign_base {
  int __val_ = 7;
};
template <class> struct optional : __optional_move_assign_base<> {
  using __base = __optional_move_assign_base;
  optional() : __base() {}
  template <class _Up, enable_if_t> optional(_Up &&);
  template <class _Up, enable_if_t<_Up ::__enable_explicit>>
  optional(_Up &&) : __base() {}
};
int main()
{
  optional<int> o;
  __CPROVER_assert(o.__val_ == 7, "base subobject initialized");
  return 0;
}
