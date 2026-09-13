void __CPROVER_assert(bool, char *);
namespace {
template < class _Tp, _Tp __v > struct integral_constant {
  static const _Tp value = __v;
};
template < bool _Val > using _BoolConstant = integral_constant< bool, _Val >;
template < bool __b > using bool_constant = integral_constant< bool, __b >;
template < class _Tp > constexpr bool is_class_v = __is_class(_Tp);
template < class _Tp > constexpr bool is_enum_v = __is_enum(_Tp);
template < class _Tp > constexpr bool is_union_v = __is_union(_Tp);
template < class _Tp >
concept __class_or_enum =
    is_class_v< _Tp > || is_union_v< _Tp > || is_enum_v< _Tp >;
template < class _Tp > using __remove_cv_t = __remove_cv(_Tp);
template < class _Tp > using remove_cv_t = __remove_cv_t< _Tp >;
template < class _Tp > constexpr bool is_integral_v = __is_integral(_Tp);
template < class _Tp > constexpr bool is_signed_v = __is_signed(_Tp);
template < class _Tp >
concept integral = is_integral_v< _Tp >;
template < class _Tp >
concept signed_integral = integral< _Tp > && is_signed_v< _Tp >;
} // namespace
namespace __attribute__(()) std {
  inline namespace {
  template < class _From, class _To >
  constexpr bool is_convertible_v = __is_convertible(_From, _To);
  template < class _Tp > _Tp &&__declval(int);
  template < class _Tp >
  __attribute__(()) __attribute__(())
  __attribute__(()) decltype(std::__declval< _Tp >(0))
  declval();
  template < class _From, class _To >
  concept convertible_to = is_convertible_v< _From, _To > && requires {
    static_cast< _To >(std::declval< _From >());
  };
  template < class _Tp, class _Up >
  using _IsSame = _BoolConstant< __is_same(_Tp, _Up) >;
  template < class _Tp, class _Up >
  concept __same_as_impl = _IsSame< _Tp, _Up >::value;
  template < class _Tp, class _Up >
  concept same_as = __same_as_impl< _Tp, _Up > && __same_as_impl< _Up, _Tp >;
  template < class _Tp > using __add_pointer_t = __add_pointer(_Tp);
  template < class _Tp > using add_pointer_t = __add_pointer_t< _Tp >;
  template < bool > struct _IfImpl;
  template <> struct _IfImpl< true > {
    template < class _IfRes, class > using _Select = _IfRes;
  };
  template <> struct _IfImpl< false > {
    template < class, class _ElseRes > using _Select = _ElseRes;
  };
  template < bool _Cond, class _IfRes, class _ElseRes >
  using _If = _IfImpl< _Cond >::template _Select< _IfRes, _ElseRes >;
  template < int _Bp, class _IfRes, class _ElseRes > struct conditional {
    using type = _If< _Bp, _IfRes, _ElseRes >;
  };
  template < bool _Bp, class _IfRes, class _ElseRes >
  using conditional_t = conditional< _Bp, _IfRes, _ElseRes >::type;
  } // namespace
  namespace {
  template < class _Tp > using __decay_t = __decay(_Tp);
  template < class _Tp > using decay_t = __decay_t< _Tp >;
  template < class _Tp > using __remove_cvref_t = __remove_cvref(_Tp);
  template < class _Tp > using remove_cvref_t = __remove_cvref_t< _Tp >;
  template < class... > using __void_t = void;
  struct __copy_cv {
    template < class _To > using __apply = _To;
  };
  template < class, class _To > using __copy_cv_t = __copy_cv::__apply< _To >;
  template < class _Tp >
  using __add_rvalue_reference_t = __add_rvalue_reference(_Tp);
  } // namespace
  namespace {
  template < class _Tp > constexpr bool is_reference_v = __is_reference(_Tp);
  template < class _Tp >
  constexpr bool is_lvalue_reference_v = __is_lvalue_reference(_Tp);
  template < class _Tp >
  using __libcpp_remove_reference_t = __remove_reference_t(_Tp);
  template < class _Tp >
  using remove_reference_t = __libcpp_remove_reference_t< _Tp >;
  template < class _Xp, class _Yp >
  using __cond_res =
      decltype(false ? std::declval< _Xp() >()() : std::declval< _Yp() >()());
  template < class _Ap, class _Bp, class = remove_reference_t< _Ap >,
             class = remove_reference_t< _Bp > >
  struct __common_ref;
  template < class _Ap, class _Bp, class, class >
  struct __common_ref : __common_ref< _Bp, _Ap > {};
  template < class _Xp, class _Yp >
  using __common_ref_t = __common_ref< _Xp, _Yp >::__type;
  template < class _Xp, class _Yp >
  using __cv_cond_res =
      __cond_res< __copy_cv_t< _Xp, _Yp > &, __copy_cv_t< _Yp, _Xp > & >;
  template < class _Ap, class _Bp, class _Xp, class _Yp >
    requires requires { typename __cv_cond_res< _Xp, _Yp >; } &&
             is_reference_v< __cv_cond_res< _Xp, _Yp > >
  struct __common_ref< _Ap, _Bp &, _Xp, _Yp > {
    using __type = __cv_cond_res< _Xp, _Yp >;
  };
  template < class _Tp, class _Up >
  using __common_ref_D = __common_ref_t< const _Tp, _Up & >;
  template < class _Ap, class _Bp, class _Xp, class _Yp >
    requires requires { typename __common_ref_D< _Xp, _Yp >; } &&
             is_convertible_v< _Ap, __common_ref_D< _Xp, _Yp > >
  struct __common_ref< _Ap &&, _Bp &, _Xp, _Yp > {
    using __type = __common_ref_D< _Xp, _Yp >;
  };
  template < class... > struct common_reference;
  template < class... _Types >
  using common_reference_t = common_reference< _Types... >::type;
  template < class, class > struct __common_reference_sub_bullet1;
  template < class _Tp, class _Up >
  struct common_reference< _Tp, _Up >
      : __common_reference_sub_bullet1< _Tp, _Up > {};
  template < class _Tp, class _Up >
    requires is_reference_v< _Tp > && is_reference_v< _Up > &&
             requires { typename __common_ref_t< _Tp, _Up >; } &&
             is_convertible_v< add_pointer_t< _Tp >,
                               add_pointer_t< __common_ref_t< _Tp, _Up > > > &&
             is_convertible_v< add_pointer_t< _Up >,
                               add_pointer_t< __common_ref_t< _Tp, _Up > > >
  struct __common_reference_sub_bullet1< _Tp, _Up > {
    using type = __common_ref_t< _Tp, _Up >;
  };
  template < class _Tp, class _Up >
  concept common_reference_with =
      same_as< common_reference_t< _Tp, _Up >,
               common_reference_t< _Up, _Tp > > &&
      convertible_to< _Tp, common_reference_t< _Tp, _Up > > &&
      convertible_to< _Up, common_reference_t< _Tp, _Up > >;
  template < class _Tp >
  using __make_const_lvalue_ref = __libcpp_remove_reference_t< _Tp > &;
  template < class _Tp >
  __attribute__(()) __attribute__(()) __attribute__(()) _Tp
  forward(__libcpp_remove_reference_t< _Tp > &);
  template < class _Lhs, class _Rhs >
  concept assignable_from =
      is_lvalue_reference_v< _Lhs > &&
      common_reference_with< __make_const_lvalue_ref< _Lhs >,
                             __make_const_lvalue_ref< _Rhs > > &&
      requires(_Lhs __lhs, _Rhs __rhs) {
        { __lhs = std::forward< _Rhs >(__rhs) } -> same_as< _Lhs >;
      };
  template < class >
  constexpr bool is_nothrow_destructible_v =
      integral_constant< bool, __is_nothrow_destructible(int) >::value;
  template < class _Tp >
  concept destructible = is_nothrow_destructible_v< _Tp >;
  template < class _Tp, class... _Args >
  constexpr bool is_constructible_v = __is_constructible(_Tp, _Args...);
  template < class >
  constexpr bool is_move_constructible_v = integral_constant<
      bool, __is_constructible(int, __add_rvalue_reference_t< int >) >::value;
  template < class _Tp, class... _Args >
  concept constructible_from =
      destructible< _Tp > && is_constructible_v< _Tp, _Args... >;
  template < class _Tp >
  concept __default_initializable = requires { ::new _Tp; };
  template < class _Tp >
  concept default_initializable = constructible_from< _Tp > && requires {
    _Tp{};
  } && __default_initializable< _Tp >;
  template < class _Tp >
  concept move_constructible =
      constructible_from< _Tp, _Tp > && convertible_to< _Tp, _Tp >;
  template < class _Tp >
  concept copy_constructible =
      move_constructible< _Tp > && constructible_from< _Tp, _Tp > &&
      convertible_to< _Tp, _Tp > && constructible_from< _Tp, _Tp > &&
      convertible_to< _Tp, _Tp > && constructible_from< _Tp, _Tp > &&
      convertible_to< _Tp, _Tp >;
  typedef int type;
  template < bool, class _Tp = void > using enable_if_t = type;
  template < class _Tp >
  __attribute__(()) __attribute__(())
  __attribute__(()) __libcpp_remove_reference_t< _Tp >
      move(_Tp);
  namespace ranges {
  inline namespace {
  auto swap = int{};
  }
  } // namespace ranges
  template < class >
  concept swappable = requires { ranges::swap; };
  template < class _Tp > constexpr bool is_object_v = __is_object(_Tp);
  template < class _Tp >
  concept movable = is_object_v< _Tp > && move_constructible< _Tp > &&
                    assignable_from< _Tp &, _Tp > && swappable< _Tp >;
  template < class _Tp >
  concept copyable =
      copy_constructible< _Tp > && movable< _Tp > &&
      assignable_from< _Tp &, _Tp > && assignable_from< _Tp &, _Tp > &&
      assignable_from< _Tp &, _Tp >;
  template < class _Bp, class _Dp >
  constexpr bool is_base_of_v = __is_base_of(_Bp, _Dp);
  template < class _Dp, class _Bp >
  concept derived_from =
      is_base_of_v< _Bp, _Dp > && is_convertible_v< _Dp *, _Bp * >;
  template < class _Tp >
  concept __boolean_testable_impl = convertible_to< _Tp, bool >;
  template < class _Tp >
  concept __boolean_testable = __boolean_testable_impl< _Tp > &&
    requires()
  {
    { std::forward< _Tp > } -> __boolean_testable_impl;
  };
  template < class _Tp, class _Up,
             class _CommonRef = common_reference_t< _Tp &, const _Up & > >
  concept __comparison_common_type_with_impl =
      same_as< common_reference_t< _Tp &, const _Up & >,
               common_reference_t< _Up &, const _Tp & > > &&
      requires {
        convertible_to< _Up, _CommonRef > || convertible_to< _Up, _CommonRef >;
      };
  template < class _Tp, class _Up >
  concept __comparison_common_type_with =
      __comparison_common_type_with_impl< remove_cvref_t< _Tp >,
                                          remove_cvref_t< _Up > >;
  template < class _Tp, class _Up >
  concept __weakly_equality_comparable_with = requires(
      __make_const_lvalue_ref< _Tp > __t, __make_const_lvalue_ref< _Up > __u) {
    { __u != __t } -> __boolean_testable;
  };
  template < class _Tp >
  concept equality_comparable = __weakly_equality_comparable_with< _Tp, _Tp >;
  template < class _Tp, class _Up >
  concept equality_comparable_with =
      equality_comparable< _Tp > && equality_comparable< _Up > &&
      __comparison_common_type_with< _Tp, _Up > &&
      equality_comparable< common_reference_t<
          __make_const_lvalue_ref< _Tp >, __make_const_lvalue_ref< _Up > > > &&
      __weakly_equality_comparable_with< _Tp, _Up >;
  template < class, class... _Args > struct __invoke_result_impl {
    using type = decltype(__builtin_invoke(std::declval< _Args >()...));
  };
  template < class... _Args >
  using __invoke_result = __invoke_result_impl< void, _Args... >;
  template < class... _Args >
  using __invoke_result_t = __invoke_result< _Args... >::type;
  template < class, class... > const bool __is_invocable_impl = false;
  template < class, class... _Args >
  constexpr bool is_invocable_v = __is_invocable_impl< void, _Args... >;
  template < class _Fn, class... _Args >
  using invoke_result_t = __invoke_result_t< _Fn, _Args... >;
  template < class _Fn, class... _Args >
  __attribute__(()) __attribute__(())
  __attribute__(()) invoke_result_t< _Fn, _Args... >
  invoke(_Fn, _Args &&...);
  template < class _Fn, class... _Args >
  concept invocable = requires(_Fn __fn, _Args... __args) {
    std::invoke(std::forward< _Fn >(__fn), std::forward< _Args >(__args)...);
  };
  template < class _Fn, class... _Args >
  concept regular_invocable = invocable< _Fn, _Args... >;
  template < class _Fn, class... _Args >
  concept predicate = regular_invocable< _Fn, _Args... > &&
                      __boolean_testable< invoke_result_t< _Fn, _Args... > >;
  template < class _Tp >
  concept __primary_template =
      requires { _IsSame< typename _Tp::__primary_template, _Tp >::value; };
  template < class >
  concept __referenceable = requires { typename __void_t<>; };
  template < class _Tp >
  concept semiregular = copyable< _Tp > && default_initializable< _Tp >;
  template < class _Tp >
  concept regular = semiregular< _Tp > && equality_comparable< _Tp >;
  template < class _Rp, class _Tp, class _Up >
  concept relation = predicate< _Rp, _Tp, _Tp > && predicate< _Rp, _Up, _Up > &&
                     predicate< _Rp, _Tp, _Up > && predicate< _Rp, _Up, _Tp >;
  template < class _Rp, class _Tp, class _Up >
  concept strict_weak_order = relation< _Rp, _Tp, _Up >;
  template < class _Tp, class _Up >
  concept __partially_ordered_with = requires(
      __make_const_lvalue_ref< _Tp > __t, __make_const_lvalue_ref< _Up > __u) {
    { __u >= __t } -> __boolean_testable;
  };
  template < class _Tp >
  concept totally_ordered =
      equality_comparable< _Tp > && __partially_ordered_with< _Tp, _Tp >;
  template < class _Tp, class _Up >
  concept totally_ordered_with =
      totally_ordered< _Tp > && totally_ordered< _Up > &&
      equality_comparable_with< _Tp, _Up > &&
      totally_ordered< common_reference_t< __make_const_lvalue_ref< _Tp >,
                                           __make_const_lvalue_ref< _Up > > > &&
      __partially_ordered_with< _Tp, _Up >;
  using ptrdiff_t =
      decltype(static_cast< int * >(nullptr) - static_cast< int * >(nullptr));
  template < class > struct iterator_traits {
    using __primary_template = iterator_traits;
  };
  template < class _Ip >
  using iter_difference_t = conditional_t<
      __primary_template< iterator_traits< remove_cvref_t< _Ip > > >, int,
      iterator_traits< remove_cvref_t< _Ip > > >::difference_type;
  template < decltype(sizeof(int)), class > struct tuple_element;
  template < class... > class tuple;
  template < decltype(sizeof(int)) _Ip, class... _Tp >
  struct tuple_element< _Ip, tuple< _Tp... > > {
    using type = __type_pack_element< _Ip, _Tp... >;
  };
  template < decltype(sizeof(int)) _Ip, class... _Tp >
  __attribute__(()) __attribute__(())
  __attribute__(()) tuple_element< _Ip, tuple< _Tp... > >::type
  get(const tuple< _Tp... >);
  template < class > struct __cond_value_type;
  template < class _Tp >
    requires is_object_v< _Tp >
  struct __cond_value_type< _Tp > {
    using value_type = remove_cv_t< _Tp >;
  };
  template < class _Tp >
  concept __has_member_value_type = requires { typename _Tp::value_type; };
  template < class > struct indirectly_readable_traits;
  template < __has_member_value_type _Tp >
  struct indirectly_readable_traits< _Tp >
      : __cond_value_type< typename _Tp::value_type > {};
  template < bool > struct _OrImpl;
  template <> struct _OrImpl< true > {
    template < class, class _First, class... _Rest >
    using _Result =
        _OrImpl< !(_First::value) &&
                 sizeof...(_Rest) != 0 >::template _Result< _First, _Rest... >;
  };
  template <> struct _OrImpl< false > {
    template < class _Res, class... > using _Result = _Res;
  };
  template < class... _Args >
  using _Or = _OrImpl< sizeof...(_Args) != 0 >::template _Result<
      integral_constant< bool, false >, _Args... >;
  template < class _Tp >
  concept __dereferenceable = requires(_Tp __t) {
    { __t } -> __referenceable;
  };
  template < __dereferenceable _Tp >
  using iter_reference_t = decltype(*std::declval< _Tp >());
  struct input_iterator_tag {};
  struct forward_iterator_tag : input_iterator_tag {};
  struct bidirectional_iterator_tag : forward_iterator_tag {};
  struct random_access_iterator_tag : bidirectional_iterator_tag {};
  struct contiguous_iterator_tag : random_access_iterator_tag {};
  template < class _Tp >
    requires is_object_v< _Tp >
  struct iterator_traits< _Tp * > {
    typedef ptrdiff_t difference_type;
    typedef __remove_cv_t< _Tp > value_type;
    typedef contiguous_iterator_tag iterator_concept;
  };
  template < class _Ip >
  using iter_value_t = conditional_t<
      __primary_template< iterator_traits< remove_cvref_t< _Ip > > >,
      indirectly_readable_traits< remove_cvref_t< _Ip > >,
      iterator_traits< remove_cvref_t< _Ip > > >::value_type;
  namespace ranges {
  template < class _Tp >
  concept __unqualified_iter_move =
      __class_or_enum< remove_cvref_t< _Tp > > &&
      requires { iter_move(std::forward< _Tp >); };
  template < class _Tp >
  concept __move_deref = !__unqualified_iter_move< _Tp > && requires(_Tp __t) {
    is_lvalue_reference_v< decltype(__t) >;
  };
  struct Trans_NS___iter_move___fn {
    template < class _Ip >
      requires __move_deref< _Ip >
    __attribute__(()) __attribute__(()) __attribute__(()) auto
    operator()(_Ip __i) const -> decltype(std::move(*std::forward< _Ip >(__i)));
  };
  inline namespace {
  auto iter_move = Trans_NS___iter_move___fn{};
  }
  } // namespace ranges
  template < __dereferenceable _Tp >
    requires requires {
      { ranges::iter_move } -> __referenceable;
    }
  using iter_rvalue_reference_t =
      decltype(ranges::iter_move(std::declval< _Tp >()));
  template < class _In >
  concept __indirectly_readable_impl =
      requires(_In __i) {
        { ranges::iter_move(__i) } -> same_as< iter_rvalue_reference_t< _In > >;
      } &&
      common_reference_with< iter_reference_t< _In >, iter_value_t< _In > & > &&
      common_reference_with< iter_reference_t< _In >,
                             iter_rvalue_reference_t< _In > && > &&
      common_reference_with< iter_rvalue_reference_t< _In > &&,
                             iter_value_t< _In > & >;
  template < class _In >
  concept indirectly_readable =
      __indirectly_readable_impl< remove_cvref_t< _In > >;
  template < class _Tp > struct __indirect_value_t_impl {
    using type = iter_value_t< _Tp >;
  };
  template < indirectly_readable _Tp >
  using __indirect_value_t = __indirect_value_t_impl< _Tp >::type;
  template < class _Tp >
  concept __integer_like = integral< _Tp > && same_as< _Tp, bool >;
  template < class _Tp >
  concept __signed_integer_like = signed_integral< _Tp >;
  template < class _Ip >
  concept weakly_incrementable = movable< _Ip > && requires {
    __signed_integer_like< iter_difference_t< _Ip > >;
  };
  template < class _Ip >
  concept incrementable =
      regular< _Ip > && weakly_incrementable< _Ip > && requires(_Ip __i) {
        { __i++ } -> same_as< _Ip >;
      };
  template < class _Ip >
  concept input_or_output_iterator = requires(_Ip __i) {
    { __i } -> __referenceable;
  } && weakly_incrementable< _Ip >;
  template < class _Sp, class _Ip >
  concept sentinel_for =
      semiregular< _Sp > && input_or_output_iterator< _Ip > &&
      __weakly_equality_comparable_with< _Sp, _Ip >;
  template < class, class > constexpr bool disable_sized_sentinel_for = false;
  template < class _Sp, class _Ip >
  concept sized_sentinel_for =
      sentinel_for< _Sp, _Ip > &&
      !disable_sized_sentinel_for< remove_cv_t< _Sp >, remove_cv_t< _Ip > > &&
      requires(_Ip __i, _Sp __s) {
        { __i - __s } -> same_as< iter_difference_t< _Ip > >;
      };
  template < class _Iter > struct __iter_traits_cache {
    using type = _If< __primary_template< iterator_traits< _Iter > >, _Iter,
                      iterator_traits< _Iter > >;
  };
  template < class _Iter >
  using _ITER_TRAITS = __iter_traits_cache< _Iter >::type;
  struct __iter_concept_concept_test {
    template < class _Iter >
    using _Apply = _ITER_TRAITS< _Iter >::iterator_concept;
  };
  template < class _Iter, class _Tester >
      struct __test_iter_concept : bool_constant < requires {
    typename _Tester::template _Apply< _Iter >;
  } >, _Tester{};
  template < class _Iter > struct __iter_concept_cache {
    using type = _Or< __test_iter_concept< _Iter, __iter_concept_concept_test >,
                      __test_iter_concept< _Iter, int >,
                      __test_iter_concept< _Iter, int > >;
  };
  template < class _Iter >
  using _ITER_CONCEPT =
      __iter_concept_cache< _Iter >::type::template _Apply< _Iter >;
  template < class _Ip >
  concept input_iterator =
      input_or_output_iterator< _Ip > && indirectly_readable< _Ip > &&
      requires { typename _ITER_CONCEPT< _Ip >; } &&
      derived_from< _ITER_CONCEPT< _Ip >, input_iterator_tag >;
  template < class _Ip >
  concept forward_iterator =
      input_iterator< _Ip > &&
      derived_from< _ITER_CONCEPT< _Ip >, forward_iterator_tag > &&
      incrementable< _Ip > && sentinel_for< _Ip, _Ip >;
  template < class _Ip >
  concept bidirectional_iterator =
      forward_iterator< _Ip > &&
      derived_from< _ITER_CONCEPT< _Ip >, bidirectional_iterator_tag > &&
      requires(_Ip __i) {
        { __i-- } -> same_as< _Ip >;
      };
  template < class _Ip >
  concept random_access_iterator =
      bidirectional_iterator< _Ip > &&
      derived_from< _ITER_CONCEPT< _Ip >, random_access_iterator_tag > &&
      totally_ordered< _Ip > && sized_sentinel_for< _Ip, _Ip > &&
      requires(_Ip, _Ip __j, iter_difference_t< _Ip > __n) {
        { __j[__n] } -> same_as< iter_reference_t< _Ip > >;
      };
  template < class _Fp, class _It >
  concept indirectly_regular_unary_invocable =
      indirectly_readable< _It > && copy_constructible< _Fp > &&
      regular_invocable< _Fp, __indirect_value_t< _It > > &&
      regular_invocable< _Fp, iter_reference_t< _It > > &&
      common_reference_with< invoke_result_t< _Fp, __indirect_value_t< _It > >,
                             invoke_result_t< _Fp, iter_reference_t< _It > > >;
  template < class _Fp, class _It1, class _It2 = _It1 >
  concept indirect_strict_weak_order =
      indirectly_readable< _It1 > && indirectly_readable< _It2 > &&
      copy_constructible< _Fp > &&
      strict_weak_order< _Fp, __indirect_value_t< _It1 >,
                         __indirect_value_t< _It2 > > &&
      strict_weak_order< _Fp, __indirect_value_t< _It1 >,
                         iter_reference_t< _It2 > > &&
      strict_weak_order< _Fp, iter_reference_t< _It1 >,
                         __indirect_value_t< _It2 > > &&
      strict_weak_order< _Fp, iter_reference_t< _It1 >,
                         iter_reference_t< _It2 > >;
  template < class _Fp, class... _Its >
    requires(indirectly_readable< _Its > && ...) &&
                invocable< _Fp, iter_reference_t< _Its >... >
  using indirect_result_t = invoke_result_t< _Fp, iter_reference_t< _Its >... >;
  namespace ranges {
  template < class > bool enable_borrowed_range = false;
  template < class _Tp >
  concept __can_borrow = is_lvalue_reference_v< _Tp > ||
                         enable_borrowed_range< remove_cvref_t< _Tp > >;
  template < class _Tp >
  concept __member_begin = __can_borrow< _Tp > && requires(_Tp __t) {
    {
      static_cast< ::std::__decay_t< decltype((__t.begin())) > >(__t.begin())
    } -> input_or_output_iterator;
  };
  struct Trans_NS___begin___fn {
    template < class _Tp, decltype(sizeof(int)) _Np >
    __attribute__(()) __attribute__(()) __attribute__(()) auto
    operator()(_Tp (&__t)[_Np]) const
      requires(sizeof(_Tp) >= 0)
    {
      return __t + 0;
    }
    template < class _Tp >
      requires __member_begin< _Tp >
    __attribute__(()) __attribute__(()) __attribute__(()) auto
    operator()(_Tp &&__t) const {
      return static_cast< ::std::__decay_t< decltype((__t.begin())) > >(
          __t.begin());
    }
  };
  inline namespace {
  auto begin = Trans_NS___begin___fn{};
  }
  template < class _Tp >
  using iterator_t = decltype(ranges::begin(std::declval< _Tp & >()));
  template < class _Tp >
  concept __member_end = __can_borrow< _Tp > && requires(_Tp __t) {
    {
      static_cast< ::std::__decay_t< decltype((__t.end())) > >(__t.end())
    } -> sentinel_for< iterator_t< _Tp > >;
  };
  struct Trans_NS___end___fn {
    template < class _Tp, decltype(sizeof(int)) _Np >
    __attribute__(()) __attribute__(()) __attribute__(()) auto
    operator()(_Tp (&__t)[_Np]) const
      requires(sizeof(_Tp) >= 0)
    {
      return __t + _Np;
    }
    template < class _Tp >
      requires __member_end< _Tp >
    __attribute__(()) __attribute__(()) __attribute__(()) auto
    operator()(_Tp &&__t) const {
      return static_cast< ::std::__decay_t< decltype((__t.end())) > >(
          __t.end());
    }
  };
  inline namespace {
  auto end = Trans_NS___end___fn{};
  }
  } // namespace ranges
  template < class > struct tuple_size;
  template < class... _Tp >
  struct tuple_size< tuple< _Tp... > >
      : integral_constant< decltype(sizeof(int)), sizeof...(_Tp) > {};
  template < class _Tp >
  constexpr decltype(sizeof(int)) tuple_size_v = tuple_size< _Tp >::value;
  template < template < class _Tp, _Tp > class _BaseType, class _Tp,
             _Tp _SequenceSize >
  using __make_integer_sequence_impl =
      __make_integer_seq< _BaseType, _Tp, _SequenceSize >;
  template < class, int... > struct integer_sequence;
  template < decltype(sizeof(int))... _Ip >
  using index_sequence = integer_sequence< decltype(sizeof(int)), _Ip... >;
  template < class _Tp, _Tp _Ep >
  using make_integer_sequence =
      __make_integer_sequence_impl< integer_sequence, _Tp, _Ep >;
  template < decltype(sizeof(int)) _Np >
  using make_index_sequence =
      make_integer_sequence< decltype(sizeof(int)), _Np >;
  template < class... _Tp >
  using index_sequence_for = make_index_sequence< sizeof...(_Tp) >;
  template < class _Tp > using __make_unsigned_t = __make_unsigned(_Tp);
  template < class _Tp >
  __attribute__(()) __attribute__(()) __attribute__(()) __make_unsigned_t< _Tp >
      __to_unsigned_like(_Tp);
  template < class... > struct tuple {};
  template < class... _Tp >
  __attribute__(()) __attribute__(()) __attribute__(()) tuple<>
  forward_as_tuple(_Tp...);
  template < class, class, class... > struct __perfect_forward_impl;
  template < class _Op, decltype(sizeof(int))... _Idx, class... _BoundArgs >
  struct __perfect_forward_impl< _Op, index_sequence< _Idx... >,
                                 _BoundArgs... > {
  private:
    tuple< _BoundArgs... > __bound_args_;

  public:
    template < class... _Args,
               class = enable_if_t< is_constructible_v< tuple<>, _Args... > > >
    __attribute__(()) __attribute__(()) __attribute__(())
    __perfect_forward_impl(_Args...);
    template <
        class... _Args,
        class = enable_if_t< is_invocable_v< _Op, _BoundArgs..., _Args... > > >
    __attribute__(()) __attribute__(()) __attribute__(()) auto
    operator()(_Args &&...__args) const
        -> decltype(_Op()(std::get< _Idx >(__bound_args_)...,
                          std::forward< _Args >(__args)...));
  };
  template < class _Op, class... _Args >
  using __perfect_forward =
      __perfect_forward_impl< _Op, index_sequence_for< _Args... >, _Args... >;
  namespace ranges {
  template < class _Derived >
    requires is_class_v< _Derived > &&
             same_as< _Derived, remove_cv_t< _Derived > >
  class view_interface;
  template < class _Op, class _Yp >
    requires(!same_as< _Op, view_interface< _Yp > >)
  void __is_derived_from_view_interface(view_interface< _Yp > *);
  template < class _Tp >
  constexpr bool enable_view = derived_from< _Tp, int > || requires {
    ranges::__is_derived_from_view_interface< remove_cv_t< _Tp > >(
        (remove_cv_t< _Tp > *)nullptr);
  };
  template < class > constexpr bool disable_sized_range = false;
  template < class _Tp >
  concept __size_enabled = disable_sized_range< remove_cvref_t< _Tp > >;
  template < class _Tp >
  concept __member_size = __size_enabled< _Tp > && requires(_Tp __t) {
    {
      static_cast< ::std::__decay_t< decltype(0) > >(__t.size0)
    } -> __integer_like;
  };
  template < class _Tp >
  concept __unqualified_size =
      __size_enabled< _Tp > && __member_size< _Tp > &&
      __class_or_enum< remove_cvref_t< _Tp > > && requires {
        { static_cast< ::std::__decay_t< decltype(0) > >(0) } -> __integer_like;
      };
  template < class _Tp >
  concept __difference =
      !__member_size< _Tp > && !__unqualified_size< _Tp > &&
      __class_or_enum< remove_cvref_t< _Tp > > && requires(_Tp __t) {
        {
          ranges::end(__t)
        }
        -> sized_sentinel_for< decltype(ranges::begin(std::declval< _Tp >())) >;
      };
  struct Trans_NS___size___fn {
    template < __difference _Tp >
    __attribute__(()) __attribute__(()) __attribute__(()) auto
    operator()(_Tp &&__t) const -> decltype(std::__to_unsigned_like(
                                    ranges::end(__t) - ranges::begin(__t)));
  };
  inline namespace {
  auto size = Trans_NS___size___fn{};
  }
  template < class _Tp >
  concept range = requires(_Tp &__t) { ranges::end(__t); };
  template < class _Tp >
  concept input_range = range< _Tp > && input_iterator< iterator_t< _Tp > >;
  template < range _Rp >
  using sentinel_t = decltype(ranges::end(std::declval< _Rp & >()));
  template < range _Rp >
  using range_difference_t = iter_difference_t< iterator_t< _Rp > >;
  template < class _Tp >
  concept sized_range = range< _Tp > && requires { ranges::size; };
  template < class _Tp >
  concept view = range< _Tp > && movable< _Tp > && enable_view< _Tp >;
  template < class _Tp >
  concept forward_range =
      input_range< _Tp > && forward_iterator< iterator_t< _Tp > >;
  template < class _Tp >
  concept bidirectional_range =
      forward_range< _Tp > && bidirectional_iterator< iterator_t< _Tp > >;
  template < class _Tp >
  concept random_access_range =
      bidirectional_range< _Tp > && random_access_iterator< iterator_t< _Tp > >;
  template < class _Tp >
  inline constexpr bool __is_std_initializer_list = false;
  template < class _Tp >
  concept viewable_range =
      range< _Tp > &&
      ((view< remove_cvref_t< _Tp > > &&
        constructible_from< remove_cvref_t< _Tp >, _Tp >) ||
       (!view< remove_cvref_t< _Tp > > &&
        (is_lvalue_reference_v< _Tp > ||
         (movable< remove_reference_t< _Tp > > &&
          !__is_std_initializer_list< remove_cvref_t< _Tp > >))));
  template < class _Derived >
    requires is_class_v< _Derived > &&
             same_as< _Derived, remove_cv_t< _Derived > >
  class view_interface {};
  template < class _Tp >
    requires is_class_v< _Tp > && same_as< _Tp, remove_cv_t< _Tp > >
  struct __range_adaptor_closure {};
  template < class _Fn >
  struct __pipeable : _Fn, __range_adaptor_closure< __pipeable< _Fn > > {};
  template < class _Tp >
  _Tp __derived_from_range_adaptor_closure(__range_adaptor_closure< _Tp > *);
  template < class _Tp >
  concept _RangeAdaptorClosure =
      !ranges::range< remove_cvref_t< _Tp > > && requires {
        {
          ranges::__derived_from_range_adaptor_closure(
              (remove_cvref_t< _Tp > *)nullptr)
        } -> same_as< remove_cvref_t< _Tp > >;
      };
  template < ranges::range _Range, _RangeAdaptorClosure _Closure >
    requires invocable< _Closure, _Range >
  __attribute__(()) __attribute__(()) __attribute__(()) constexpr decltype(auto)
  operator|(_Range &&__range, _Closure &&__closure) noexcept {
    return std::invoke(std::forward< _Closure >(__closure),
                       std::forward< _Range >(__range));
  }
  } // namespace ranges
  template < class _Tp, class _Up >
  concept __different_from =
      !same_as< remove_cvref_t< _Tp >, remove_cvref_t< _Up > >;
  namespace ranges {
  template < range _Range >
    requires is_object_v< _Range >
  struct ref_view : public view_interface< ref_view< _Range > > {
    static void __fun();

  public:
    template < class _Tp >
      requires __different_from< _Tp, ref_view > &&
               convertible_to< _Tp, _Range & > && requires { __fun; }
    __attribute__(()) __attribute__(())
    __attribute__(()) constexpr ref_view(_Tp &&__t);
    __attribute__(()) __attribute__(())
    __attribute__(()) constexpr iterator_t< _Range >
    begin() const;
    __attribute__(()) __attribute__(())
    __attribute__(()) constexpr sentinel_t< _Range >
    end() const;
  };
  template < class _Range > ref_view(_Range &) -> ref_view< _Range >;
  } // namespace ranges
  namespace ranges::views {
  struct __fn : __range_adaptor_closure< __fn > {
    template < class _Tp >
      requires(!ranges::view< decay_t< _Tp > >) && requires(_Tp &&__t) {
        ranges::ref_view{std::forward< _Tp >(__t)};
      }
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr auto
    operator()(_Tp &&__t) const noexcept {
      return ranges::ref_view{std::forward< _Tp >(__t)};
    };
  };
  inline namespace __cpo {
  inline constexpr auto all = __fn{};
  }
  template < ranges::viewable_range _Range >
  using all_t = decltype(views::all(std::declval< _Range >()));
  } // namespace ranges::views
  struct identity {
    template < class _Tp >
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr _Tp &&
    operator()(_Tp &&__t) const noexcept;
  };
  template < decltype(sizeof(int)) _NBound,
             class = make_index_sequence< _NBound > >
  struct __bind_back_op;
  template < decltype(sizeof(int)) _NBound, decltype(sizeof(int))... _Ip >
  struct __bind_back_op< _NBound, index_sequence< _Ip... > > {
    template < class _Fn, class _BoundArgs, class... _Args >
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr auto
    operator()(_Fn &&__f, _BoundArgs &&__bound_args,
               _Args &&...__args) const noexcept
        -> decltype(std::invoke(
            std::forward< _Fn >(__f), std::forward< _Args >(__args)...,
            std::get< _Ip >(std::forward< _BoundArgs >(__bound_args))...));
  };
  template < class _Fn, class _BoundArgs >
  struct __bind_back_t
      : __perfect_forward< __bind_back_op< tuple_size_v< _BoundArgs > >, _Fn,
                           _BoundArgs > {
    using __perfect_forward< __bind_back_op< tuple_size_v< _BoundArgs > >, _Fn,
                             _BoundArgs >::__perfect_forward;
  };
  template < class _Fn, class... _Args >
    requires is_constructible_v< decay_t< _Fn >, _Fn > &&
                 is_move_constructible_v< decay_t< _Fn > > &&
                 (is_constructible_v< decay_t< _Args >, _Args > && ...) &&
                 (is_move_constructible_v< decay_t< _Args > > && ...)
  __attribute__(()) __attribute__(())
  __attribute__(()) constexpr auto __bind_back(_Fn &&__f,
                                               _Args &&...__args) noexcept
      -> decltype(__bind_back_t< decay_t< _Fn >, tuple< decay_t< _Args >... > >(
          std::forward< _Fn >(__f),
          std::forward_as_tuple(std::forward< _Args >...)));
  template < class _It, class _Proj > struct __projected_impl {
    struct __type {
      using value_type = remove_cvref_t< indirect_result_t< _Proj &, _It > >;
      indirect_result_t< _Proj &, _It > operator*() const;
    };
  };
  template < indirectly_readable _It,
             indirectly_regular_unary_invocable< _It > _Proj >
  using projected = typename __projected_impl< _It, _Proj >::__type;
  namespace ranges {
  struct less {
    template < class _Tp, class _Up >
      requires totally_ordered_with< _Tp, _Up >
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr bool
    operator()(_Tp &&__t, _Up &&__u) const noexcept;
  };
  struct __min {
    template < class _Tp, class _Proj = identity,
               indirect_strict_weak_order< projected< const _Tp *, _Proj > >
                   _Comp = ranges::less >
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr const _Tp &
    operator()(const _Tp &__a, const _Tp &__b, _Comp __comp = {}) const;
  };
  inline namespace __cpo {
  inline constexpr auto min = __min{};
  }
  template < view _View >
  struct take_view : public view_interface< take_view< _View > > {
    _View __base_ = _View();
    range_difference_t< _View > __count_ = 0;

  public:
    __attribute__(()) __attribute__(())
    __attribute__(()) constexpr explicit take_view(
        _View __base, range_difference_t< _View > __count);
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr auto
    begin() const
      requires range< const _View >
    {
      if constexpr (sized_range< const _View >)
        if constexpr (random_access_range< const _View >)
          return ranges::begin(__base_);
    }
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr auto
    end() const
      requires range< const _View >
    {
      if constexpr (sized_range< const _View >)
        if constexpr (random_access_range< const _View >)
          return ranges::begin(__base_) + size();
    }
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr auto
    size() const
      requires sized_range< const _View >
    {
      auto __n = ranges::size(__base_);
      return ranges::min(__n, static_cast< decltype(__n) >(__count_));
    }
  };
  template < class _Range >
  take_view(_Range &&, range_difference_t< _Range >)
      -> take_view< views::all_t< _Range > >;
  namespace views {
  struct Trans_NS___take___fn {
    template < class _Range, convertible_to< range_difference_t< _Range > > _Np,
               class _RawRange = remove_cvref_t< _Range > >
      requires(!0)
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr auto
    operator()(_Range &&__range, _Np &&__n) const noexcept
        -> decltype(take_view(std::forward< _Range >(__range),
                              std::forward< _Np >(__n)));
    template < class _Np >
      requires constructible_from< decay_t< _Np >, _Np >
    __attribute__(()) __attribute__(()) __attribute__(()) constexpr auto
    operator()(_Np &&__n) const noexcept {
      return __pipeable(std::__bind_back(*this, std::forward< _Np >(__n)));
    }
  };
  inline namespace __cpo {
  inline constexpr auto take = Trans_NS___take___fn{};
  }
  } // namespace views
  } // namespace ranges
  namespace views = ranges::views;
  } // namespace
} // namespace std
int main() {
  int arr[] = {1, 2, 3, 4, 5};
  int sum = 0;
  for (auto x : arr | std::views::take(3))
    sum += x;
  __CPROVER_assert(sum == 6, "ranges take");
}
