// libc++ __bind_back_op shape (the <ranges> pipe's invoke chain):
//   template <size_t _NBound, class = make_index_sequence<_NBound>>
//   struct __bind_back_op;
//   template <size_t _NBound, size_t... _Ip>
//   struct __bind_back_op<_NBound, index_sequence<_Ip...>> { ... };
// Three N5008-grounded ingredients, each formerly broken:
//   * [temp.param]/14: the defaulted second parameter references the
//     preceding NON-TYPE parameter (preceding expression parameters
//     were not bound when the default was materialized);
//   * [intseq.make]: the clang builtin __make_integer_seq used BARE as
//     a type (the resolve_scope intercept only covered qualified uses);
//   * [temp.variadic]/5: a nested non-type pack pattern deduced to TWO
//     or more values -- per-element substitution went through the
//     scalar convenience entry, so `integer_sequence<ul, _Ip...>`
//     substituted to `<ul,0,0>` and the specialization never matched.
// clang builtins => CLANG mode; clang++ runs this clean.
extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp, _Tp... _Ip> struct integer_sequence {};
template <long... _Ip>
using index_sequence = integer_sequence<unsigned long, _Ip...>;
template <long _Ep>
using make_index_sequence = __make_integer_seq<integer_sequence, unsigned long, _Ep>;
template <long _NBound, class = make_index_sequence<_NBound>>
struct __bind_back_op;
template <long _NBound, unsigned long... _Ip>
struct __bind_back_op<_NBound, integer_sequence<unsigned long, _Ip...>> {
  static const int value = 1 + sizeof...(_Ip);
};
int main()
{
  __CPROVER_assert(__bind_back_op<2>::value == 3, "defaulted seq param");
  return 0;
}
