extern "C" void __CPROVER_assert(bool, const char *);
               namespace std {
                     typedef long int ptrdiff_t;
             }
                extern "C++"         namespace std __attribute__(()) {
              template < int __v> struct integral_constant {
              static constexpr int value = __v;
              using type = integral_constant;
            };
              template <bool __v> using __bool_constant = integral_constant< __v>;
      template <typename _Tp> struct remove_cv {
              using type = __remove_cv(_Tp);
            };
              template <typename _Tp> using __remove_cv_t = typename remove_cv<_Tp>::type;
              template <typename> struct __is_integral_helper : public __bool_constant<false> {
    };
              template <> struct __is_integral_helper<long> : public __bool_constant<true> {
    };
              template <typename _Tp>   struct is_integral : public __is_integral_helper<__remove_cv_t<_Tp>>::type {
    };
                                                              template <typename _Tp, typename _Up = _Tp &&> _Up __declval(int);
              template <typename _Tp>   auto declval() noexcept -> decltype(__declval<_Tp>(0));
                       template <typename _Tp> using remove_cv_t = typename remove_cv<_Tp>::type;
              template <typename _Tp> struct remove_reference {
              using type = __remove_reference(_Tp);
            };
              template <typename _Tp>   using remove_reference_t = typename remove_reference<_Tp>::type;
              template <typename _Tp>   using make_unsigned_t = int;
              template <typename _Tp> struct decay {
              using type = __decay(_Tp);
            };
              template <typename _Tp> using __decay_t = typename decay<_Tp>::type;
              template <typename _Tp> struct __success_type {
              using type = _Tp;
            };
                       template <typename _Tp, typename _Tag>   struct __result_of_success : __success_type<_Tp> {
            };
              template <bool, bool, typename _Functor, typename... _ArgTypes>   struct __result_of_impl;
              template <typename _Fn, typename... _Args>     static __result_of_success<         decltype(std::declval<_Fn>()(std::declval<_Args>()...)), int>     _S_test(int);
      struct __result_of_other_impl {
                      };
              template <typename _Functor, typename... _ArgTypes>   struct __result_of_impl<false, false, _Functor, _ArgTypes...>       : private __result_of_other_impl {
              using type = decltype(_S_test<_Functor, _ArgTypes...>(0));
            };
              template <typename _Functor, typename... _ArgTypes>   struct __invoke_result       : public __result_of_impl<             __bool_constant<__is_member_object_pointer(int)> ::value,             __bool_constant<__is_member_function_pointer(int)> ::value,             _Functor, _ArgTypes...>::type {
    };
              template <typename _Tp> using decay_t = typename decay<_Tp>::type;
                       template <typename _Tp>   inline constexpr bool is_integral_v = is_integral<_Tp>::value;
              template <typename _Tp> inline constexpr bool is_array_v = __is_array(_Tp);
              template <typename _Tp> inline constexpr bool is_lvalue_reference_v = false;
              template <typename _Tp>   inline constexpr bool is_lvalue_reference_v<_Tp &> = true;
              template <typename _Tp> inline constexpr bool is_enum_v = __is_enum(_Tp);
              template <typename _Tp> inline constexpr bool is_union_v = __is_union(_Tp);
              template <typename _Tp> inline constexpr bool is_class_v = __is_class(_Tp);
              template <typename _Tp>   inline constexpr bool is_reference_v = __is_reference(_Tp);
              template <typename _Tp> inline constexpr bool is_object_v = __is_object(_Tp);
              template <typename _Tp, typename... _Args>   inline constexpr bool is_constructible_v = __is_constructible(_Tp, _Args...);
              template <typename _Tp, unsigned _Idx = 0>   inline constexpr unsigned long extent_v = 0;
              template <typename _Tp, typename _Up>   inline constexpr bool is_same_v = __is_same(_Tp, _Up);
              template <typename _From, typename _To>   inline constexpr bool is_convertible_v = __is_convertible(_From, _To);
              template <typename _Tp> struct remove_cvref {
              using type = __remove_cvref(_Tp);
            };
              template <typename _Tp>   using remove_cvref_t = typename remove_cvref<_Tp>::type;
              template <typename _Tp>   using type_identity_t = int;
              template <typename _Tp>   inline constexpr bool is_bounded_array_v = __is_bounded_array(_Tp);
              template <typename _Xp, typename _Yp>   using __cond_res = decltype(false ? declval<_Xp()>()() : declval<_Yp()>()());
              template <typename... _Tp> struct common_reference;
              template <typename... _Tp>   using common_reference_t = typename common_reference<_Tp...>::type;
              template <typename _Tp1, typename _Tp2, int _Bullet = 1>   struct __common_reference_impl       : __common_reference_impl<_Tp1, _Tp2, _Bullet + 1> {
    };
              template <typename _Tp1, typename _Tp2>   struct common_reference<_Tp1, _Tp2> : __common_reference_impl<_Tp1, _Tp2> {
    };
              template <typename _Tp1, typename _Tp2>     requires is_reference_v<_Tp1> && is_reference_v<_Tp2> &&              requires {
          typename __cond_res<_Tp1, _Tp2>;
          }
              struct __common_reference_impl<_Tp1, _Tp2, 3> {
              using type = __cond_res<_Tp1, _Tp2>;
            };
               namespace __detail {
             template <typename _Tp, typename _Up>   concept __same_as = std::is_same_v<_Tp, _Up>;
             }
               template <typename _Tp, typename _Up>   concept same_as =       __detail::__same_as<_Tp, _Up> && __detail::__same_as<_Up, _Tp>;
               namespace __detail {
             template <typename _Tp, typename _Up>   concept __different_from = !   same_as<remove_cvref_t<_Tp>, remove_cvref_t<_Up>>;
             }
                template <typename _Derived, typename _Base>   concept derived_from =       __is_base_of(_Base, _Derived) &&       is_convertible_v<const volatile _Derived *, const volatile _Base *>;
               template <typename _From, typename _To>   concept convertible_to =       is_convertible_v<_From, _To> &&       requires {
           static_cast<_To>(std::declval<_From>());
           };
               template <typename _Tp, typename _Up>   concept common_reference_with =       same_as<common_reference_t<_Tp, _Up>, common_reference_t<_Up, _Tp>> &&       convertible_to<_Tp, common_reference_t<_Tp, _Up>> &&       convertible_to<_Up, common_reference_t<_Tp, _Up>>;
               template <typename _Tp>   concept integral = is_integral_v<_Tp>;
               namespace __detail {
             template <typename _Tp> using __cref = const remove_reference_t<_Tp> &;
             template <typename _Tp>   concept __class_or_enum =       is_class_v<_Tp> || is_union_v<_Tp> || is_enum_v<_Tp>;
             template <typename _Tp> constexpr bool __destructible_impl = false;
             template <typename _Tp>     requires requires(_Tp &__t) {
                        {
       __t.~_Tp() }
         noexcept;
                      }
             constexpr bool __destructible_impl<_Tp> = true;
             template <typename _Tp>   constexpr bool __destructible = __destructible_impl<_Tp>;
             }
                template <typename _Lhs, typename _Rhs>   concept assignable_from =       is_lvalue_reference_v<_Lhs> &&       common_reference_with<__detail::__cref<_Lhs>, __detail::__cref<_Rhs>> &&       requires(_Lhs __lhs, _Rhs && __rhs) {
                   {
         __lhs = static_cast<_Rhs &&>(__rhs) }
           -> same_as<_Lhs>;
                 };
               template <typename _Tp>   concept destructible = __detail::__destructible<_Tp>;
               template <typename _Tp, typename... _Args>   concept constructible_from =       destructible<_Tp> && is_constructible_v<_Tp, _Args...>;
               template <typename _Tp>   concept default_initializable =       constructible_from<_Tp> && requires {
           ::new _Tp;
           };
               template <typename _Tp>   concept move_constructible =       constructible_from<_Tp, _Tp> && convertible_to<_Tp, _Tp>;
               template <typename _Tp>   concept copy_constructible =       move_constructible<_Tp> && constructible_from<_Tp, _Tp &> &&       convertible_to<_Tp &, _Tp> && constructible_from<_Tp, const _Tp &> &&       convertible_to<const _Tp &, _Tp> && constructible_from<_Tp, const _Tp> &&       convertible_to<const _Tp, _Tp>;
               namespace ranges {
                     struct _Swap {
   };
                      inline namespace _Cpo {
           inline constexpr _Swap swap;
           }
             }
                template <typename _Tp>   concept swappable = requires {
           ranges::swap;
           };
               template <typename _Tp>   concept movable = is_object_v<_Tp> && move_constructible<_Tp> &&                     assignable_from<_Tp &, _Tp> && swappable<_Tp>;
               template <typename _Tp>   concept copyable =       copy_constructible<_Tp> && movable<_Tp> &&       assignable_from<_Tp &, _Tp &> && assignable_from<_Tp &, const _Tp &> &&       assignable_from<_Tp &, const _Tp>;
               template <typename _Tp>   concept semiregular = copyable<_Tp> && default_initializable<_Tp>;
               namespace __detail {
             template <typename _Tp>   concept __boolean_testable_impl = convertible_to<_Tp, bool>;
             template <typename _Tp>   concept __boolean_testable =       __boolean_testable_impl<_Tp> && requires(_Tp &&__t) {
                                                 {
                                                 !static_cast<_Tp &&>(__t)                                           }
         -> __boolean_testable_impl;
                                               };
             template <typename _Tp, typename _Up>   concept __weakly_eq_cmp_with =       requires(__detail::__cref<_Tp> __t, __detail::__cref<_Up> __u) {
                 {
       __t == __u }
         -> __boolean_testable;
               };
             }
                template <typename _Tp>   concept equality_comparable = __detail::__weakly_eq_cmp_with<_Tp, _Tp>;
               namespace __detail {
             template <typename _Tp, typename _Up>   concept __partially_ordered_with = requires(       const remove_reference_t<_Tp> &__t, const remove_reference_t<_Up> &__u) {
                                                {
       __u >= __t }
         -> __boolean_testable;
                                              };
             }
               template <typename _Tp>   concept totally_ordered =       equality_comparable<_Tp> && __detail::__partially_ordered_with<_Tp, _Tp>;
               template <typename _Tp>   concept regular = semiregular<_Tp> && equality_comparable<_Tp>;
               template <typename _Tp>   __attribute__(()) constexpr _Tp *__addressof(_Tp & __r) noexcept;
               template <typename _Tp>   constexpr _Tp &&forward(typename std::remove_reference<_Tp>::type &                           __t) noexcept;
               template <typename _Tp>   constexpr       typename std::remove_reference<_Tp>::type &&move(_Tp && __t) noexcept;
      struct input_iterator_tag {
    };
      struct forward_iterator_tag : public input_iterator_tag {
    };
      struct bidirectional_iterator_tag : public forward_iterator_tag {
    };
      struct random_access_iterator_tag : public bidirectional_iterator_tag {
    };
               template <typename _Iterator> struct iterator_traits;
               namespace __detail {
             template <typename _Tp> using __with_ref = _Tp &;
             template <typename _Tp>   concept __can_reference = requires {
         typename __with_ref<_Tp>;
         };
             template <typename _Tp>   concept __dereferenceable = requires(_Tp &__t) {
                                         {
       *__t }
         -> __can_reference;
                                       };
             }
                template <__detail::__dereferenceable _Tp>   using iter_reference_t = decltype(*std::declval<_Tp &>());
               namespace ranges {
             namespace __imove {
           template <typename _Tp> using __iter_ref_t = decltype(*std::declval<_Tp>());
    template <typename _Tp> struct __result {
            using type = __iter_ref_t<_Tp>;
          };
    struct _IterMove {
         private:                     public:     template <typename _Tp> using __type = typename __result<_Tp>::type;
         };
           }
              }
                template <__detail::__dereferenceable _Tp>     requires __detail::__can_reference<                  ranges::__imove::_IterMove::__type<_Tp &>>   using iter_rvalue_reference_t = ranges::__imove::_IterMove::__type<_Tp &>;
               template <typename> struct incrementable_traits;
               namespace __detail {
             template <typename _Iter> struct __iter_traits_impl {
             using type = iterator_traits<_Iter>;
           };
             template <typename _Iter, typename _Tp = _Iter>   using __iter_traits = typename __iter_traits_impl<_Iter>::type;
             template <typename _Tp>   using __iter_diff_t =       typename __iter_traits<_Tp, incrementable_traits<_Tp>>::difference_type;
             }
                template <typename _Tp>   using iter_difference_t = __detail::__iter_diff_t<remove_cvref_t<_Tp>>;
               template <typename> struct indirectly_readable_traits;
               namespace __detail {
             template <typename _Tp>   using __iter_value_t =       typename __iter_traits<_Tp, indirectly_readable_traits<_Tp>>::value_type;
             }
               template <typename _Tp>   using iter_value_t = __detail::__iter_value_t<remove_cvref_t<_Tp>>;
               namespace __detail {
             template <typename _Iter>   concept __cpp17_iterator = requires(_Iter __it) {
                                             *__it++       -> __can_reference;
                                      }
           && copyable<_Iter>;
             template <typename _Iter> struct __iter_concept_impl;
             template <typename _Iter>     requires requires {
         typename __iter_traits<_Iter>::iterator_concept;
         }
             struct __iter_concept_impl<_Iter> {
             using type = typename __iter_traits<_Iter>::iterator_concept;
           };
             template <typename _Iter>   using __iter_concept = typename __iter_concept_impl<_Iter>::type;
             template <typename _In>   concept __indirectly_readable_impl =       requires {
         typename iter_value_t<_In>;
         }
           &&       common_reference_with<iter_reference_t<_In> &&, iter_value_t<_In> &> &&       common_reference_with<iter_reference_t<_In> &&,                             iter_rvalue_reference_t<_In> &&> &&       common_reference_with<iter_rvalue_reference_t<_In> &&,                             const iter_value_t<_In> &>;
             }
                template <typename _In>   concept indirectly_readable =       __detail::__indirectly_readable_impl<remove_cvref_t<_In>>;
               namespace ranges::__detail {
             class __max_diff_type;
             class __max_size_type;
             template <typename _Tp>   concept __cv_bool = same_as<const volatile _Tp, const volatile bool>;
             template <typename _Tp>   concept __integral_nonbool = integral<_Tp> && !   __cv_bool<_Tp>;
             template <typename _Tp>   concept __is_integer_like =       __integral_nonbool<_Tp> || same_as<_Tp, __max_diff_type> ||       same_as<_Tp, __max_size_type>;
             }
                template <typename _Iter>   concept weakly_incrementable = movable<_Iter> && requires(_Iter __i) {
                                                                {
                                                                ++__i                                                        }
           -> same_as<_Iter &>;
                                                              };
               template <typename _Iter>   concept incrementable =       regular<_Iter> && weakly_incrementable<_Iter> && requires(_Iter __i) {
                                                                    {
                                                                    __i++                                                            }
           -> same_as<_Iter>;
                                                                  };
               template <typename _Iter>   concept input_or_output_iterator = requires(_Iter __i) {
                                                  {
         *__i }
           -> __detail::__can_reference;
                                                }
             && weakly_incrementable<_Iter>;
               template <typename _Sent, typename _Iter>   concept sentinel_for =       semiregular<_Sent> && input_or_output_iterator<_Iter> &&       __detail::__weakly_eq_cmp_with<_Sent, _Iter>;
               template <typename _Sent, typename _Iter>   inline constexpr bool disable_sized_sentinel_for = false;
               template <typename _Sent, typename _Iter>   concept sized_sentinel_for = sentinel_for<_Sent, _Iter> && !   disable_sized_sentinel_for<remove_cv_t<_Sent>, remove_cv_t<_Iter>>       &&requires(const _Iter &__i, const _Sent &__s) {
                     {
         __s - __i }
           -> same_as<iter_difference_t<_Iter>>;
                   };
               template <typename _Iter>   concept input_iterator =       input_or_output_iterator<_Iter> && indirectly_readable<_Iter> &&       requires {
           typename __detail::__iter_concept<_Iter>;
           }
             &&       derived_from<__detail::__iter_concept<_Iter>, input_iterator_tag>;
               template <typename _Iter>   concept forward_iterator =       input_iterator<_Iter> &&       derived_from<__detail::__iter_concept<_Iter>, forward_iterator_tag> &&       incrementable<_Iter> && sentinel_for<_Iter, _Iter>;
               template <typename _Iter>   concept bidirectional_iterator = forward_iterator<_Iter> &&                                    derived_from<__detail::__iter_concept<_Iter>,                                                 bidirectional_iterator_tag> &&                                    requires(_Iter __i) {
                                                {
         __i-- }
           -> same_as<_Iter>;
                                              };
               template <typename _Iter>   concept random_access_iterator =       bidirectional_iterator<_Iter> &&       derived_from<__detail::__iter_concept<_Iter>,                    random_access_iterator_tag> &&       totally_ordered<_Iter> && sized_sentinel_for<_Iter, _Iter> &&       requires(_Iter __i, const _Iter __j, const iter_difference_t<_Iter> __n) {
                   {
         __j[__n] }
           -> same_as<iter_reference_t<_Iter>>;
                 };
               namespace ranges::__access {
             using std::__detail::__class_or_enum;
             template <typename _Tp>   concept __member_begin = requires(_Tp &__t) {
                                      {
                                      ::std::__decay_t<decltype((__t.begin()))>()                                }
         -> input_or_output_iterator;
                                    };
             template <typename _Tp>   concept __adl_begin = __class_or_enum<remove_reference_t<_Tp>> &&                         requires {
                                   {
                                   ::std::__decay_t<decltype(0)>()                             }
         -> input_or_output_iterator;
                                 };
             template <typename _Tp>     requires is_array_v<_Tp> || __member_begin<_Tp &> || __adl_begin<_Tp &>   constexpr auto __begin(_Tp &__t) {
             if constexpr (is_array_v<_Tp>)       return __t + 0;
             else if constexpr (__member_begin<_Tp &>)       return __t.begin();
           }
             }
                namespace __detail {
             template <typename _Tp>   using __range_iter_t =       decltype(ranges::__access::__begin(std::declval<_Tp &>()));
             }
                                                       struct contiguous_iterator_tag : public random_access_iterator_tag {
    };
               template <typename _Tp>     requires is_object_v<_Tp>   struct iterator_traits<_Tp *> {
               using iterator_concept = contiguous_iterator_tag;
               using value_type = remove_cv_t<_Tp>;
               using difference_type = ptrdiff_t;
             };
               template <typename _Tp>   constexpr inline const _Tp &min(const _Tp &__a, const _Tp &__b) {
               return __a;
             }
               namespace ranges {
             template <typename> inline constexpr bool disable_sized_range = false;
             template <typename _Tp> inline constexpr bool enable_borrowed_range = false;
             namespace __detail {
           template <integral _Tp> constexpr auto __to_unsigned_like(_Tp __t) noexcept {
           return static_cast<make_unsigned_t<_Tp>>(__t);
         }
           template <typename _Tp>   concept __maybe_borrowed_range =       is_lvalue_reference_v<_Tp> || enable_borrowed_range<remove_cvref_t<_Tp>>;
           }
              namespace __access {
           using std::__detail::__range_iter_t;
           using std::ranges::__detail::__maybe_borrowed_range;
           struct _Begin {
         public:     template <__maybe_borrowed_range _Tp>       requires is_array_v<remove_reference_t<_Tp>> || __member_begin<_Tp> ||                __adl_begin<_Tp>     constexpr auto operator()(_Tp &&__t) const noexcept {
           if constexpr (is_array_v<remove_reference_t<_Tp>>)             return __t + 0;
               else if constexpr (__member_begin<_Tp>)         return __t.begin();
         }
         };
           template <typename _Tp>   concept __member_end = requires(_Tp &__t) {
                                  {
                                  ::std::__decay_t<decltype((__t.end()))>()                              }
       -> sentinel_for<__range_iter_t<_Tp>>;
                                };
           template <typename _Tp>   concept __adl_end = __class_or_enum<remove_reference_t<_Tp>> &&                       requires {
                               {
                               ::std::__decay_t<decltype(0)>()                           }
       -> sentinel_for<__range_iter_t<_Tp>>;
                             };
           struct _End {
         public:     template <__maybe_borrowed_range _Tp>       requires is_bounded_array_v<remove_reference_t<_Tp>> ||                __member_end<_Tp> || __adl_end<_Tp>     constexpr auto operator()(_Tp &&__t) const noexcept {
           if constexpr (is_bounded_array_v<remove_reference_t<_Tp>>)             return __t + extent_v<remove_reference_t<_Tp>>;
               else if constexpr (__member_end<_Tp>)         return __t.end();
         }
         };
           template <typename _Tp>   concept __member_size = !   disable_sized_range<remove_cvref_t<_Tp>> &&requires {
                                                      {
                                                      ::std::__decay_t<decltype(0)>()                                                  }
                                                        -> __detail::__is_integer_like;
                                                    };
           template <typename _Tp>   concept __adl_size = __class_or_enum<remove_reference_t<_Tp>> && !   disable_sized_range<remove_cvref_t<_Tp>> &&requires {
                                                      {
                                                      ::std::__decay_t<decltype(0)>()                                                  }
                                                        -> __detail::__is_integer_like;
                                                    };
           template <typename _Tp>   concept __sentinel_size =       requires(_Tp &__t) {
               __detail::__to_unsigned_like(_End{
 }
      (__t)-_Begin{
 }
      (__t));
             };
           struct _Size {
         public:     template <typename _Tp>       requires is_bounded_array_v<remove_reference_t<_Tp>> ||                __member_size<_Tp> || __adl_size<_Tp> || __sentinel_size<_Tp>     constexpr auto operator()(_Tp &&__t) const noexcept {
           if constexpr (is_bounded_array_v<remove_reference_t<_Tp>>)         return extent_v<remove_reference_t<_Tp>>;
           else if constexpr (__sentinel_size<_Tp>)         return __detail::__to_unsigned_like(_End{
 }
    (__t)-_Begin{
 }
    (__t));
         }
         };
           }
              inline namespace _Cpo {
           inline constexpr ranges::__access::_Begin begin;
           inline constexpr ranges::__access::_End end;
           inline constexpr ranges::__access::_Size size;
           }
              template <typename _Tp>   concept range = requires {
         ranges::end;
         };
             template <typename _Tp> using iterator_t = std::__detail::__range_iter_t<_Tp>;
             template <range _Range>   using sentinel_t = decltype(ranges::end(std::declval<_Range &>()));
             template <range _Range>   using range_difference_t = iter_difference_t<iterator_t<_Range>>;
             template <typename _Tp>   concept sized_range = range<_Tp> && requires {
         ranges::size;
         };
             template <typename _Derived>     requires is_class_v<_Derived> && same_as<_Derived, remove_cv_t<_Derived>>   class view_interface;
             namespace __detail {
           template <typename _Tp, typename _Up>     requires(!same_as<_Tp, view_interface<_Up>>)   void __is_derived_from_view_interface_fn(const _Tp &,                                            const view_interface<_Up> &);
           template <typename _Tp>   concept __is_derived_from_view_interface =       requires(_Tp __t) {
       __is_derived_from_view_interface_fn(__t, __t);
       };
           }
                       template <typename _Tp>   inline constexpr bool enable_view =       derived_from<_Tp, int> ||       __detail::__is_derived_from_view_interface<_Tp>;
             template <typename _Tp>   concept view = range<_Tp> && movable<_Tp> && enable_view<_Tp>;
             template <typename _Tp>   concept input_range = range<_Tp> && input_iterator<iterator_t<_Tp>>;
             template <typename _Tp>   concept forward_range = input_range<_Tp> && forward_iterator<iterator_t<_Tp>>;
             template <typename _Tp>   concept bidirectional_range =       forward_range<_Tp> && bidirectional_iterator<iterator_t<_Tp>>;
             template <typename _Tp>   concept random_access_range =       bidirectional_range<_Tp> && random_access_iterator<iterator_t<_Tp>>;
             namespace __detail {
           template <typename _Tp> inline constexpr bool __is_initializer_list = false;
           }
             template <typename _Tp>   concept viewable_range = range<_Tp> &&                            ((view<remove_cvref_t<_Tp>> &&                              constructible_from<remove_cvref_t<_Tp>, _Tp>) ||                             (!view<remove_cvref_t<_Tp>> &&                              (is_lvalue_reference_v<_Tp> || 0)));
             }
               template <typename _Res, typename _Fn, typename... _Args>   constexpr _Res __invoke_impl( _Fn && __f, _Args && ...__args) {
               return std::forward<_Fn>(__f)(std::forward<_Args>(__args)...);
             }
               template <typename _Callable, typename... _Args>   constexpr typename __invoke_result<_Callable, _Args...>::type __invoke(       _Callable && __fn, _Args && ...__args) noexcept {
               using __result = __invoke_result<_Callable, _Args...>;
               return std::__invoke_impl<typename __result::type>( std::forward<_Callable>(__fn),                                       std::forward<_Args>(__args)...);
             }
               namespace ranges {
             namespace __detail {
           using std::__detail::__different_from;
           }
              template <typename _Derived>     requires is_class_v<_Derived> && same_as<_Derived, remove_cv_t<_Derived>>   class view_interface {
   };
             };
               template <int _Back, typename _Fd, typename... _BoundArgs> struct _Binder {
               template <typename _Fn, typename... _Args>     explicit constexpr _Binder( _Fn &&__fn, _Args &&...__args) noexcept          {
   }
               template <typename _Tp, typename... _CallArgs>     static constexpr decltype(auto) _S_call(_Tp &&__g,                                             _CallArgs &&...__call_args) {
               if constexpr (sizeof...(_BoundArgs) > 1)         return 0;
               else {
                           {
               _Tp &&__trans_tmp_1 = std::forward<_Tp>(__g);
               {
                 _Tp &&__trans_tmp_2 = std::forward<_Tp>(__g);
                 return std::__invoke(__trans_tmp_1._M_fd,                              std::forward<_CallArgs>(__call_args)...,                              __trans_tmp_2._M_bound_args);
               }
             }
              }
             }
             private:                _Fd _M_fd;
               decltype(0) _M_bound_args;
             };
               template <typename _Fn, typename... _Args>   using _Bind_back_t =       _Binder<(sizeof...(_Args) > 0), decay_t<_Fn>, decay_t<_Args>...>;
               namespace ranges {
             namespace views::__adaptor {
           template <typename _Adaptor, typename... _Args>   concept __adaptor_invocable =       requires {
       std::declval<_Adaptor>()(declval<_Args>()...);
       };
           template <typename _Adaptor, typename... _Args>   concept __adaptor_partial_app_viable =       (_Adaptor::_S_arity > 1) &&       (sizeof...(_Args) == _Adaptor::_S_arity - 1) &&       (constructible_from<decay_t<_Args>, _Args> && ...);
           template <typename _Adaptor, typename... _Args> struct _Partial;
    template <typename _Derived> struct _RangeAdaptorClosure {
  };
           template <typename _Tp, typename _Up>     requires(!same_as<_Tp, _RangeAdaptorClosure<_Up>>)   void __is_range_adaptor_closure_fn(const _Tp &,                                      const _RangeAdaptorClosure<_Up> &);
           template <typename _Tp>   concept __is_range_adaptor_closure =       requires(_Tp __t) {
       __adaptor::__is_range_adaptor_closure_fn(__t, __t);
       };
           template <typename _Self, typename _Range>     requires __is_range_adaptor_closure<_Self> &&              __adaptor_invocable<_Self, _Range>   constexpr auto operator|(_Range &&__r, _Self &&__self) {
           return std::forward<_Self>(__self)(std::forward<_Range>(__r));
         }
                   template <typename _Derived> struct _RangeAdaptor {
           template <typename... _Args>       requires __adaptor_partial_app_viable<_Derived, _Args...>     constexpr auto operator()(_Args &&...__args) const {
           return _Partial<_Derived, decay_t<_Args>...>{
    0, std::forward<_Args>...};
         }
         };
           template <typename _Adaptor, typename... _Args>   struct _Partial : _RangeAdaptorClosure<_Partial<_Adaptor, _Args...>> {
           using _Binder = _Bind_back_t<_Adaptor, _Args...>;
           _Binder _M_binder;
           template <typename... _Ts>     constexpr _Partial( _Ts &&...__args)         : _M_binder(0, _Adaptor(), std::forward<_Ts>...) {
 }
           template <typename _Range>       requires __adaptor_invocable<_Adaptor, _Range, const _Args &...>     constexpr auto operator()(_Range &&__r) const {
           return _Binder::_S_call(_M_binder, std::forward<_Range>(__r));
         }
         };
           }
              template <range _Range>     requires is_object_v<_Range>   struct ref_view : public view_interface<ref_view<_Range>> {
           private:     _Range *_M_r;
             static void _S_fun();
           public:     template <__detail::__different_from<ref_view> _Tp>       requires convertible_to<_Tp, _Range &> && requires {
       _S_fun;
       }
             constexpr ref_view(_Tp &&__t) noexcept         : _M_r(               std::__addressof(static_cast<_Range &>(std::forward<_Tp>(__t)))) {
  }
             constexpr iterator_t<_Range> begin() const {
       return ranges::begin(*_M_r);
       }
             constexpr sentinel_t<_Range> end() const {
       return ranges::end(*_M_r);
       }
           };
             template <typename _Range> ref_view(_Range &) -> ref_view<_Range>;
             template <range _Range>     requires movable<_Range> &&              (!__detail::__is_initializer_list<remove_cv_t<_Range>>)   class owning_view : public view_interface<owning_view<_Range>> {
   };
             namespace views {
           namespace __detail {
         template <typename _Range>   concept __can_ref_view = requires {
     ref_view{
    std::declval<_Range>()};
     };
         template <typename _Range>   concept __can_owning_view = requires {
     owning_view{
    std::declval<_Range>};
     };
         }
            struct _All  {
           template <viewable_range _Range>       requires view<decay_t<_Range>> || __detail::__can_ref_view<_Range> ||                __detail::__can_owning_view<_Range>     constexpr auto operator()(_Range &&__r) const noexcept {
           if constexpr (view<decay_t<_Range>>)         return std::forward;
           else if constexpr (__detail::__can_ref_view<_Range>)         return ref_view{
    std::forward<_Range>(__r)};
           else         return owning_view{
    std::forward<_Range>};
         }
         };
           inline constexpr _All all;
           template <viewable_range _Range>   using all_t = decltype(all(std::declval<_Range>()));
           }
              template <view _Vp> struct take_view : public view_interface<take_view<_Vp>> {
             _Vp _M_base = _Vp();
             range_difference_t<_Vp> _M_count = 0;
           public:     constexpr explicit take_view(_Vp __base, range_difference_t<_Vp> __count)         : _M_base(std::move(__base)), _M_count() {
  }
             constexpr auto begin() const       requires range<const _Vp>     {
             if constexpr (sized_range<const _Vp>)             if constexpr (random_access_range<const _Vp>)           return ranges::begin(_M_base);
                     }
             constexpr auto end() const       requires range<const _Vp>     {
             if constexpr (sized_range<const _Vp>)             if constexpr (random_access_range<const _Vp>)           return ranges::begin(_M_base) + size();
                     }
             constexpr auto size() const       requires sized_range<const _Vp>     {
             auto __n = ranges::size(_M_base);
             return std::min(__n, static_cast<decltype(__n)>(_M_count));
           }
           };
             template <typename _Range>   take_view(_Range &&, range_difference_t<_Range>)       -> take_view<views::all_t<_Range>>;
             namespace views {
           namespace __detail {
         template <typename _Range> inline constexpr bool __is_empty_view = false;
         template <typename _Range, typename _Dp>   concept __can_take_view =       requires {
     take_view(std::declval<_Range>(), std::declval<_Dp>());
     };
         }
            struct _Take : __adaptor::_RangeAdaptor<_Take> {
           template <viewable_range _Range, typename _Dp = range_difference_t<_Range>>       requires __detail::__can_take_view<_Range, _Dp>     constexpr auto operator()(_Range &&__r, type_identity_t<_Dp> __n) const {
           using _Tp = remove_cvref_t<_Range>;
           if constexpr (__detail::__is_empty_view<_Tp>)         return _Tp();
           else         return take_view(std::forward<_Range>(__r), __n);
         }
           using _RangeAdaptor::operator();
           static constexpr int _S_arity = 2;
         };
           inline constexpr _Take take;
           }
              }
                namespace views = ranges::views;
             }
                int main() {
               int arr[] = {
          1, 2, 3, 4, 5};
               int sum = 0;
               for (auto x : arr | std::views::take(3))     sum += x;
               int reached = 1;
               __CPROVER_assert(reached == 1, "the pipe converts");
               __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
             }
