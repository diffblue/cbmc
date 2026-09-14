extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp, _Tp... _Ip>
struct integer_sequence
{
  static constexpr int size = sizeof...(_Ip);
};
// libc++: the builtin is wrapped in an impl alias whose first
// parameter is a TEMPLATE-TEMPLATE parameter.
template <template <class _T, _T...> class _BaseType, class _Tp,
          _Tp _SequenceSize>
using __make_integer_sequence_impl =
  __make_integer_seq<_BaseType, _Tp, _SequenceSize>;
template <class _Tp, _Tp _Ep>
using make_integer_sequence =
  __make_integer_sequence_impl<integer_sequence, _Tp, _Ep>;
template <unsigned long _Np>
using make_index_sequence = make_integer_sequence<unsigned long, _Np>;
int main()
{
  __CPROVER_assert(
    make_index_sequence<3>::size == 3, "size via TT-param impl alias");
  return 0;
}
