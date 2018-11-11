/*******************************************************************\

Module: Small shared two-way pointer

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UTIL_SMALL_SHARED_TWO_WAY_PTR_H
#define CPROVER_UTIL_SMALL_SHARED_TWO_WAY_PTR_H

#include <type_traits>
#include <limits>
#include <utility>

#include "invariant.h"

template <typename Num>
class small_shared_two_way_pointeet;

/// This class is similar to small_shared_ptrt and boost's intrusive_ptr. Like
/// those, it stores the use count with the pointed-to object instead of in a
/// separate control block. Additionally, it uses the MSB of the use count to
/// indicate the type of the managed object (which is either of type U or V).
///
/// A possible use case is the implementation of data structures with sharing
/// that consist of two different types of objects (such as a tree with internal
/// nodes and leaf nodes). Storing the type with the use count avoids having to
/// keep a separate `type` member or using `typeid` or `dynamic_cast`. Moreover,
/// since the shared pointer is aware of the concrete type of the object being
/// stored, it can delete it without requiring a virtual destructor or custom
/// delete function (like std::shared_ptr).
template <typename U, typename V>
class small_shared_two_way_ptrt final
{
public:
  typedef decltype(std::declval<U>().use_count()) use_countt;

  typedef small_shared_two_way_pointeet<use_countt> pointeet;

  static_assert(std::is_base_of<pointeet, U>::value, "");
  static_assert(std::is_base_of<pointeet, V>::value, "");

  small_shared_two_way_ptrt() = default;

  explicit small_shared_two_way_ptrt(U *u) : p(u)
  {
    PRECONDITION(u != nullptr);
    PRECONDITION(u->use_count() == 0);

    p->set_derived_u();
    p->increment_use_count();
  }

  explicit small_shared_two_way_ptrt(V *v) : p(v)
  {
    PRECONDITION(v != nullptr);
    PRECONDITION(v->use_count() == 0);

    p->set_derived_v();
    p->increment_use_count();
  }

  small_shared_two_way_ptrt(const small_shared_two_way_ptrt &rhs) : p(rhs.p)
  {
    PRECONDITION(is_same_type(rhs));

    if(p)
    {
      p->increment_use_count();
    }
  }

  small_shared_two_way_ptrt(small_shared_two_way_ptrt &&rhs)
  {
    PRECONDITION(is_same_type(rhs));

    swap(rhs);
  }

  small_shared_two_way_ptrt &operator=(const small_shared_two_way_ptrt &rhs)
  {
    PRECONDITION(is_same_type(rhs));

    small_shared_two_way_ptrt copy(rhs);
    swap(copy);
    return *this;
  }

  small_shared_two_way_ptrt &operator=(small_shared_two_way_ptrt &&rhs)
  {
    PRECONDITION(is_same_type(rhs));

    swap(rhs);
    return *this;
  }

  ~small_shared_two_way_ptrt()
  {
    if(!p)
    {
      return;
    }

    auto use_count = p->use_count();

    if(use_count == 1)
    {
      if(p->is_derived_u())
      {
        U *u = static_cast<U *>(p);
        delete u;
      }
      else
      {
        V *v = static_cast<V *>(p);
        delete v;
      }
    }
    else
    {
      p->decrement_use_count();
    }
  }

  void swap(small_shared_two_way_ptrt &rhs)
  {
    PRECONDITION(is_same_type(rhs));

    std::swap(p, rhs.p);
  }

  use_countt use_count() const
  {
    return p ? p->use_count() : 0;
  }

  /// Checks if converting the held raw pointer to `U*` is valid
  bool is_derived_u() const
  {
    return p == nullptr || p->is_derived_u();
  }

  /// Checks if converting the held raw pointer to `V*` is valid
  bool is_derived_v() const
  {
    return p == nullptr || p->is_derived_v();
  }

  pointeet *get() const
  {
    return p;
  }

  U *get_derived_u() const
  {
    PRECONDITION(is_derived_u());

    return static_cast<U *>(p);
  }

  V *get_derived_v() const
  {
    PRECONDITION(is_derived_v());

    return static_cast<V *>(p);
  }

  /// Checks if the raw pointers held by `*this` and `other` both can be
  /// converted to either U* or V*
  bool is_same_type(const small_shared_two_way_ptrt &other) const
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
  pointeet *p = nullptr;
};

template <typename U, typename V, typename... Ts>
small_shared_two_way_ptrt<U, V> make_shared_derived_u(Ts &&... ts)
{
  return small_shared_two_way_ptrt<U, V>(new U(std::forward<Ts>(ts)...));
}

template <typename U, typename V, typename... Ts>
small_shared_two_way_ptrt<U, V> make_shared_derived_v(Ts &&... ts)
{
  return small_shared_two_way_ptrt<U, V>(new V(std::forward<Ts>(ts)...));
}

template <typename U, typename V>
bool operator==(
  const small_shared_two_way_ptrt<U, V> &lhs,
  const small_shared_two_way_ptrt<U, V> &rhs)
{
  return lhs.get() == rhs.get();
}

template <typename U, typename V>
bool operator!=(
  const small_shared_two_way_ptrt<U, V> &lhs,
  const small_shared_two_way_ptrt<U, V> &rhs)
{
  return lhs.get() != rhs.get();
}

template <typename Num>
class small_shared_two_way_pointeet
{
public:
  static_assert(std::is_unsigned<Num>::value, "");

  static const int bit_idx = std::numeric_limits<Num>::digits - 1;
  static const Num mask = ~((Num)1 << bit_idx);

  small_shared_two_way_pointeet() = default;

  // The use count shall be unaffected
  small_shared_two_way_pointeet(const small_shared_two_way_pointeet &rhs)
  {
  }

  // The use count shall be unaffected
  small_shared_two_way_pointeet &
  operator=(const small_shared_two_way_pointeet &rhs)
  {
    return *this;
  }

  Num use_count() const
  {
    return use_count_ & mask;
  }

  void increment_use_count()
  {
    PRECONDITION((use_count_ & mask) < mask);

    use_count_++;
  }

  void decrement_use_count()
  {
    PRECONDITION((use_count_ & mask) > 0);

    use_count_--;
  }

  void set_derived_u()
  {
    use_count_ &= mask;
  }

  void set_derived_v()
  {
    use_count_ |= ~mask;
  }

  bool is_derived_u() const
  {
    return !(use_count_ & ~mask);
  }

  bool is_derived_v() const
  {
    return (use_count_ & ~mask) != 0;
  }

  bool is_same_type(const small_shared_two_way_pointeet &other) const
  {
    return !((use_count_ ^ other.use_count_) & ~mask);
  }

private:
  Num use_count_ = 0;
};

#endif
