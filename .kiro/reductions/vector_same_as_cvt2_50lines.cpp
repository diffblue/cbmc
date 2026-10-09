void __CPROVER_assert();
template <int> struct integral_constant;
template <bool _Val> using _BoolConstant = integral_constant<_Val>;
template <class _Tp, class _Up>
using _IsSame = _BoolConstant<__is_same(_Tp, _Up)>;
template <bool, class, class> using _If = int;
template <class _Tp, class _Up>
concept __same_as_impl = _IsSame<_Tp, _Up>::value;
template <class _Tp, class _Up>
concept same_as = __same_as_impl<_Up, _Tp>;
template <class> struct common_reference;
template <class... _Types>
using common_reference_t = common_reference<_Types...>::type;
template <class, class _Up>
concept common_reference_with = same_as<_Up, common_reference_t<_Up>>;
struct bidirectional_iterator_tag;
struct random_access_iterator_tag;
template <class _In>
concept __indirectly_readable_impl = common_reference_with<_In, _In>;
template <class _In>
concept indirectly_readable = __indirectly_readable_impl<_In>;
template <class _Ip>
concept input_iterator = indirectly_readable<_Ip>;
template <class _Ip>
concept forward_iterator = input_iterator<_Ip>;
template <class>
concept bidirectional_iterator = forward_iterator<bidirectional_iterator_tag>;
template <class _Ip>
concept random_access_iterator = bidirectional_iterator<_Ip>;
template <class _Tp> using __make_unsigned_t = __make_unsigned(_Tp);
using type = __make_unsigned_t<int>;
template <class> struct reverse_iterator {
  using iterator_concept =
      _If<random_access_iterator<int>, random_access_iterator_tag,
          bidirectional_iterator_tag>;
};
using size_type = int;
template <class> struct basic_string {
  typedef int value_type;
  typedef reverse_iterator<int>;
  basic_string &replace(size_type, size_type, const value_type *, size_type);
};
extern template basic_string<char> &
basic_string<char>::replace(size_type, size_type, value_type const *,
                            size_type);
