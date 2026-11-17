template <int __v> struct integral_constant {
  static const int value = __v;
};
template <bool, class> using __enable_if_t = int;
using ::wprintf __attribute__((__using_if_exists__));
template <class> struct basic_string {
  int __r_;
  basic_string(basic_string &&)
      : __r_([](basic_string __s) -> decltype(__s) {}) {}
  template <__enable_if_t<integral_constant<false>::value, int> = 0>
  basic_string(char *);
};
basic_string Trans_NS_literals___throw_invalid_type_format_error___trans_tmp_2 =
    basic_string<char>("");
