#ifndef CPROVER_UTIL_VISITOR_GENERATOR_H
#define CPROVER_UTIL_VISITOR_GENERATOR_H

template <typename... Ts>
struct typelistt
{
};

////////////////////////////////////////////////////////////////////////////////

template <typename... Ts>
struct visitor_generatort;

template <typename... Ts>
struct visitor_generatort<typelistt<Ts...>> : visitor_generatort<Ts...>
{
  using visitor_generatort<Ts...>::visit;
};

template <typename T, typename... Ts>
struct visitor_generatort<T, Ts...> : visitor_generatort<Ts...>
{
  virtual void visit(T) = 0;
  using visitor_generatort<Ts...>::visit;
};

template <typename T>
struct visitor_generatort<T>
{
  virtual ~visitor_generatort() = default;
  virtual void visit(T) = 0;
};

////////////////////////////////////////////////////////////////////////////////

template <typename... Ts>
struct const_visitor_generatort;

template <typename... Ts>
struct const_visitor_generatort<typelistt<Ts...>>
  : const_visitor_generatort<Ts...>
{
  using const_visitor_generatort<Ts...>::visit;
};

template <typename T, typename... Ts>
struct const_visitor_generatort<T, Ts...> : const_visitor_generatort<Ts...>
{
  virtual void visit(T) const = 0;
  using const_visitor_generatort<Ts...>::visit;
};

template <typename T>
struct const_visitor_generatort<T>
{
  virtual ~const_visitor_generatort() = default;
  virtual void visit(T) const = 0;
};

////////////////////////////////////////////////////////////////////////////////

template <typename... Ts>
struct defaulted_visitor_generatort;

template <typename Base, typename... Ts>
struct defaulted_visitor_generatort<Base, typelistt<Ts...>>
  : defaulted_visitor_generatort<Base, typelistt<Ts...>, Ts...>
{
  using defaulted_visitor_generatort<Base, typelistt<Ts...>, Ts...>::visit;
};

template <typename Base, typename Typelist, typename T, typename... Ts>
struct defaulted_visitor_generatort<Base, Typelist, T, Ts...>
  : defaulted_visitor_generatort<Base, Typelist, Ts...>
{
  void visit(T t) override
  {
    this->visit(static_cast<Base>(t));
  }
  using defaulted_visitor_generatort<Base, Typelist, Ts...>::visit;
};

template <typename Base, typename Typelist, typename T>
struct defaulted_visitor_generatort<Base, Typelist, T>
  : visitor_generatort<Typelist>
{
  void visit(T t) override
  {
    this->visit(static_cast<Base>(t));
  }
  virtual void visit(Base base) = 0;
  using visitor_generatort<Typelist>::visit;
};

////////////////////////////////////////////////////////////////////////////////

template <typename... Ts>
struct const_defaulted_visitor_generatort;

template <typename Base, typename... Ts>
struct const_defaulted_visitor_generatort<Base, typelistt<Ts...>>
  : const_defaulted_visitor_generatort<Base, typelistt<Ts...>, Ts...>
{
  using const_defaulted_visitor_generatort<Base,
                                           typelistt<Ts...>,
                                           Ts...>::visit;
};

template <typename Base, typename Typelist, typename T, typename... Ts>
struct const_defaulted_visitor_generatort<Base, Typelist, T, Ts...>
  : const_defaulted_visitor_generatort<Base, Typelist, Ts...>
{
  void visit(T t) const override
  {
    this->visit(static_cast<Base>(t));
  }
  using const_defaulted_visitor_generatort<Base, Typelist, Ts...>::visit;
};

template <typename Base, typename Typelist, typename T>
struct const_defaulted_visitor_generatort<Base, Typelist, T>
  : const_visitor_generatort<Typelist>
{
  void visit(T t) const override
  {
    this->visit(static_cast<Base>(t));
  }
  virtual void visit(Base base) const = 0;
  using const_visitor_generatort<Typelist>::visit;
};

#endif // CPROVER_UTIL_VISITOR_GENERATOR_H
