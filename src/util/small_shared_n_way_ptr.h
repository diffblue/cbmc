/*******************************************************************\

Module: Small shared n-way pointer

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UTIL_SMALL_SHARED_N_WAY_PTR_H
#define CPROVER_UTIL_SMALL_SHARED_N_WAY_PTR_H

#include <limits>
#include <tuple>
#include <type_traits>
#include <utility>

#include "invariant.h"

/// Get the type with the given index in the parameter pack
template <std::size_t I, typename... Ts>
struct get_typet
{
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename std::tuple_element<I, std::tuple<Ts...>>::type type;
};

template <std::size_t N, typename Num>
class small_shared_n_way_pointee_baset;

// Struct to hold the static method destruct() to destruct the pointee of a
// small shared n-way pointer.
//
// Note: This functionality should ideally be in a private static method of
// small_shared_n_way_ptrt, but partial template specializations are not allowed
// within other templates, hence it is defined at global scope.
template <std::size_t I, typename pointee_baset, typename... Ts>
struct destructt
{
  static void destruct(pointee_baset *p)
  {
    if(p->template is_derived<I>())
    {
      typedef typename get_typet<I, Ts...>::type pointeet;
      static_assert(
        std::is_base_of<pointee_baset, pointeet>::value,
        "indexed pointee type must be a subclass of the pointee base");

      delete static_cast<pointeet *>(p);
    }
    else
    {
      destructt<I - 1, pointee_baset, Ts...>::destruct(p);
    }
  }
};

template <typename pointee_baset, typename... Ts>
struct destructt<0, pointee_baset, Ts...>
{
  static void destruct(pointee_baset *p)
  {
    PRECONDITION(p->template is_derived<0>());

    typedef typename get_typet<0, Ts...>::type pointeet;
    static_assert(
      std::is_base_of<pointee_baset, pointeet>::value,
      "indexed pointee type must be a subclass of the pointee base");

    delete static_cast<pointeet *>(p);
  }
};

/// This class is similar to small_shared_ptrt and boost's intrusive_ptr. Like
/// those, it stores the use count with the pointed-to object instead of in a
/// separate control block. Additionally, it uses the MSBs of the use count to
/// indicate the type of the managed object (which is of one of the types in the
/// parameter pack Ts).
///
/// A possible use case is the implementation of data structures with sharing
/// that consist of several different types of nodes (such as a tree with
/// internal nodes and leaf nodes). Storing the type with the use count avoids
/// having to keep a separate `type` member or using `typeid` or `dynamic_cast`.
/// Moreover, since the shared pointer is aware of the concrete type of the
/// object being stored, it can delete it without requiring a virtual destructor
/// or custom delete function (like std::shared_ptr).
///
/// \tparam Ts parameter pack of the different types the small shared n-way
///   pointer can point to
template <typename... Ts>
class small_shared_n_way_ptrt final
{
public:
  static const std::size_t num_types =
    std::tuple_size<std::tuple<Ts...>>::value;

  static_assert(
    num_types >= 2,
    "parameter pack should contain at least two types");

  typedef decltype(std::declval<typename get_typet<0, Ts...>::type>()
                     .get_use_count()) use_countt;

  typedef small_shared_n_way_pointee_baset<num_types, use_countt> pointee_baset;

  small_shared_n_way_ptrt() = default;

  /// Static factory method to construct a small shared n-way pointer, pointing
  /// to the given object *p of type Ts[I], which must be a subclass of
  /// small_shared_n_way_pointee_baset<len(Ts), Num>.
  ///
  /// \tparam I index of a type in the parameter pack Ts
  /// \param p pointer to an object of type Ts[I]
  /// \return a small shared n-way pointer pointing to p
  template <std::size_t I>
  static small_shared_n_way_ptrt<Ts...>
  create_small_shared_n_way_ptr(typename get_typet<I, Ts...>::type *p)
  {
    PRECONDITION(p != nullptr);
    PRECONDITION(p->get_use_count() == 0);

    p->template set_derived<I>();
    p->increment_use_count();

    return small_shared_n_way_ptrt<Ts...>(p);
  }

  small_shared_n_way_ptrt(const small_shared_n_way_ptrt &rhs) : p(rhs.p)
  {
    PRECONDITION(is_same_type(rhs));

    if(p)
    {
      p->increment_use_count();
    }
  }

  small_shared_n_way_ptrt(small_shared_n_way_ptrt &&rhs)
  {
    PRECONDITION(is_same_type(rhs));

    swap(rhs);
  }

  small_shared_n_way_ptrt &operator=(const small_shared_n_way_ptrt &rhs)
  {
    PRECONDITION(is_same_type(rhs));

    small_shared_n_way_ptrt copy(rhs);
    swap(copy);
    return *this;
  }

  small_shared_n_way_ptrt &operator=(small_shared_n_way_ptrt &&rhs)
  {
    PRECONDITION(is_same_type(rhs));

    swap(rhs);
    return *this;
  }

  ~small_shared_n_way_ptrt()
  {
    destruct();
  }

  /// Clears this shared pointer. Decreases the use count of the pointed-to
  /// object (if any) by one.
  void reset()
  {
    destruct();
    p = nullptr;
  }

  void swap(small_shared_n_way_ptrt &rhs)
  {
    PRECONDITION(is_same_type(rhs));

    std::swap(p, rhs.p);
  }

  /// Get the use count of the pointed-to object
  ///
  /// \return the use count of the pointed-to object
  use_countt use_count() const
  {
    return p ? p->get_use_count() : 0;
  }

  /// Check if converting the held raw pointer to type Ts[I] is valid
  ///
  /// \tparam I index into the parameter pack Ts
  template <std::size_t I>
  bool is_derived() const
  {
    return p == nullptr || p->template is_derived<I>();
  }

  /// Get base type pointer to the managed object
  ///
  /// \return pointer to the managed object, as type pointer to
  ///   small_shared_n_way_pointee_baset (the common base type of all types in
  ///   Ts)
  pointee_baset *get() const
  {
    return p;
  }

  /// Get pointer to the managed object
  ///
  /// \return pointer to the managed object, cast to type pointer to Ts[I]
  template <std::size_t I>
  typename get_typet<I, Ts...>::type *get_derived() const
  {
    PRECONDITION(is_derived<I>());

    return static_cast<typename get_typet<I, Ts...>::type *>(p);
  }

  /// Checks if the raw pointers held by `*this` and `other` both can be
  /// converted to a pointer to the same type (of a type in the parameter pack
  /// Ts)
  bool is_same_type(const small_shared_n_way_ptrt &other) const
  {
    if(p == nullptr || other.p == nullptr)
      return true;

    return p->is_same_type(*other.p);
  }

  explicit operator bool() const
  {
    return p != nullptr;
  }

private:
  template <typename T>
  explicit small_shared_n_way_ptrt(T *p) : p(p)
  {
  }

  void destruct()
  {
    if(!p)
    {
      return;
    }

    if(p->get_use_count() > 1)
    {
      p->decrement_use_count();
      return;
    }

    destructt<num_types - 1, pointee_baset, Ts...>::destruct(p);
  }

  pointee_baset *p = nullptr;
};

/// Constructs a small shared n-way pointer, with two possible pointee types
/// (i.e., n = 2), and constructs an object of either type U (when I = 0) or
/// type V (when I = 1) pointed to by the shared pointer. Arguments ts are
/// passed to the constructor of U or V. U and V must be subclasses of
/// small_shared_n_way_pointee_baset<2, Num>.
///
/// \tparam I index of the type of object to construct (0 -> U, 1 -> V)
/// \tparam U first possible pointee type
/// \tparam V second possible pointee type
/// \tparam Ts types of arguments to pass to the constructor of U or V
/// \param ts arguments to pass to the constructor of U or V
template <std::size_t I, typename U, typename V, typename... Ts>
small_shared_n_way_ptrt<U, V> make_shared_2(Ts &&... ts)
{
  return small_shared_n_way_ptrt<U, V>::template create_small_shared_n_way_ptr<
    I>(new typename get_typet<I, U, V>::type(std::forward<Ts>(ts)...));
}

/// Constructs a small shared n-way pointer, with three possible pointee types
/// (i.e., n = 3), and constructs an object of either type U (when I = 0), type
/// V (when I = 1), or type W (when I = 2), pointed to by the shared pointer.
/// Arguments ts are passed to the constructor of U, V, or W. U, V, and W must
/// be subclasses of small_shared_n_way_pointee_baset<3, Num>.
///
/// \tparam I index of the type of object to construct (0 -> U, 1 -> V)
/// \tparam U first possible pointee type
/// \tparam V second possible pointee type
/// \tparam W third possible pointee type
/// \tparam Ts types of arguments to pass to the constructor of U or V
/// \param ts arguments to pass to the constructor of U or V
template <std::size_t I, typename U, typename V, typename W, typename... Ts>
small_shared_n_way_ptrt<U, V, W> make_shared_3(Ts &&... ts)
{
  return small_shared_n_way_ptrt<U, V, W>::
    template create_small_shared_n_way_ptr<I>(
      new typename get_typet<I, U, V, W>::type(std::forward<Ts>(ts)...));
}

template <typename... Ts>
bool operator==(
  const small_shared_n_way_ptrt<Ts...> &lhs,
  const small_shared_n_way_ptrt<Ts...> &rhs)
{
  return lhs.get() == rhs.get();
}

template <typename... Ts>
bool operator!=(
  const small_shared_n_way_ptrt<Ts...> &lhs,
  const small_shared_n_way_ptrt<Ts...> &rhs)
{
  return lhs.get() != rhs.get();
}

template <std::size_t N, typename Num>
class small_shared_n_way_pointee_baset
{
public:
  static_assert(std::is_unsigned<Num>::value, "Num must be an unsigned type");

  small_shared_n_way_pointee_baset() = default;

  // The use count shall be unaffected
  small_shared_n_way_pointee_baset(const small_shared_n_way_pointee_baset &)
  {
  }

  // The use count shall be unaffected
  small_shared_n_way_pointee_baset &
  operator=(const small_shared_n_way_pointee_baset &)
  {
    return *this;
  }

  Num get_use_count() const
  {
    return use_count & use_count_mask;
  }

  void increment_use_count()
  {
    PRECONDITION(get_use_count() < use_count_mask);

    ++use_count;
  }

  void decrement_use_count()
  {
    PRECONDITION(get_use_count() > 0);

    --use_count;
  }

  template <std::size_t I>
  void set_derived()
  {
    static_assert(I < N, "type index shall be within bounds");

    use_count &= use_count_mask;
    use_count |= I << use_count_bit_width;
  }

  template <std::size_t I>
  bool is_derived() const
  {
    static_assert(I < N, "type index shall be within bounds");

    return ((use_count & ~use_count_mask) >> use_count_bit_width) == I;
  }

  bool is_same_type(const small_shared_n_way_pointee_baset &other) const
  {
    return !((use_count ^ other.use_count) & ~use_count_mask);
  }

private:
  Num use_count = 0;

  static const int bit_width = std::numeric_limits<Num>::digits;

  static constexpr std::size_t num_bits(const std::size_t n)
  {
    return n < 2 ? 1 : 1 + num_bits(n >> 1);
  }

  static const std::size_t type_bit_width = num_bits(N);

  static const std::size_t use_count_bit_width =
    (std::size_t)bit_width - type_bit_width;

  static const Num use_count_mask = ((Num)1 << use_count_bit_width) - 1;
};

#endif // CPROVER_UTIL_SMALL_SHARED_N_WAY_PTR_H
