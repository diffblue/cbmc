class environmentt
{
public:
  static environmentt java() {
    environmentt env;
    env.int_type_=java_int_type();
    env.char_type_=java_int_type();
    env.array_type_=array_typet(env.char_type_, infinity_exprt(env.int_type_));
    env.string_type_=refined_string_typet(env.int_type_, env.char_type_);
    return env;
  }

  template<
    typename T,
    typename std::enable_if<std::is_convertible<T, exprt>::value, int>::type=0>
  T make_expr(T&& expr)
  { return std::move(expr); }

  constant_exprt make_expr(char i)
  { return from_integer(i, char_type_); }

  template<
    typename T,
    typename std::enable_if<std::is_integral<T>::value, int>::type=0>
  constant_exprt make_expr(const T& i)
  { return from_integer(i, int_type_); }

  template<
    typename T,
    typename std::enable_if<std::is_same<T, std::string>::value, int>::type=0>
  string_exprt make_expr(const T &str)
  {
    const constant_exprt length=make_expr(str.length());
    array_exprt content(array_type_);
    for(const char ch : str)
      content.copy_to_operands(make_expr(ch));
    return string_exprt(length, content, string_type_);
  }

  template<
    typename T,
    typename std::enable_if<
      std::is_convertible<T, std::string>::value &&
      !std::is_same<T, std::string>::value, int>::type=0>
  string_exprt make_expr(const T &str)
  { return make_expr(std::string(str)); }

  template<typename...Args>
  function_application_exprt make_expr(
    const dstringt &id,
    typet return_type,
    Args&&... args)
  {
    function_application_exprt func(symbol_exprt(id), return_type);
    func.arguments() = { make_expr(std::forward<Args>(args))... };
    return func;
  }

  struct_exprt make_struct_expr(std::map<dstringt, exprt> members)
  {
    struct_typet type;
    for (const auto& pair : members) {
      type.components().push_back({ pair.first, pair.second.type() });
    }
    struct_exprt expr(type);
    for (const auto& pair : members) {
      expr.operands().push_back(pair.second);
    }
    return expr;
  }
private:
  environmentt()=default;

  typet int_type_;
  typet char_type_;
  typet array_type_;
  typet string_type_;
};
