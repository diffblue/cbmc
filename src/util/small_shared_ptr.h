/*******************************************************************\

Module: Small intrusive shared pointers

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_SMALL_SHARED_PTR_H
#define CPROVER_UTIL_SMALL_SHARED_PTR_H

#include <iosfwd>  // ostream
#include <utility> // swap

// TODO We should liberally scatter `constexpr`s and `noexcept`s on platforms
// that support them.

/// This class is really similar to boost's intrusive_pointer, but can be a bit
/// simpler seeing as we're only using it one place.
/// The idea is that the pointed-to object stores its reference-count
/// internally, which is more space-efficient than storing it in a separate
/// control block (which is what shared_ptr does).
template <typename T>
class small_shared_ptrt final
{
public:
  small_shared_ptrt() = default;

  explicit small_shared_ptrt(T *t) : t_(t)
  {
    if(t_)
    {
      pointee_increment_use_count(*t_);
    }
  }

  small_shared_ptrt(const small_shared_ptrt &rhs) : t_(rhs.t_)
  {
    if(t_)
    {
      pointee_increment_use_count(*t_);
    }
  }

  small_shared_ptrt &operator=(const small_shared_ptrt &rhs)
  {
    auto copy(rhs);
    swap(copy);
    return *this;
  }

  small_shared_ptrt(small_shared_ptrt &&rhs)
  {
    swap(rhs);
  }

  small_shared_ptrt &operator=(small_shared_ptrt &&rhs)
  {
    swap(rhs);
    return *this;
  }

  ~small_shared_ptrt()
  {
    if(!t_)
    {
      return;
    }
    if(pointee_use_count(*t_) == 1)
    {
      delete t_;
      return;
    }
    pointee_decrement_use_count(*t_);
  }

  void swap(small_shared_ptrt &rhs)
  {
    std::swap(t_, rhs.t_);
  }

  T *get() const
  {
    return t_;
  }

  T &operator*() const
  {
    return *t_;
  }

  T *operator->() const
  {
    return t_;
  }

  auto use_count() const -> decltype(pointee_use_count(std::declval<T>()))
  {
    return t_ ? pointee_use_count(*t_) : 0;
  }

  explicit operator bool() const
  {
    return t_ != nullptr;
  }

private:
  T *t_ = nullptr;
};

template <typename T>
std::ostream &operator<<(std::ostream &os, const small_shared_ptrt<T> &ptr)
{
  return os << ptr.get();
}

/// This function is similar to std::make_unique and std::make_shared, and
/// should be the preferred way of creating small_shared_ptrs.
/// The public constructors of small_shared_ptr are just provided to keep the
/// class design similar to that of unique_ptr and shared_ptr, but in
/// practice they should not be used directly.
template <typename T, typename... Ts>
small_shared_ptrt<T> make_small_shared_ptr(Ts &&... ts)
{
  return small_shared_ptrt<T>(new T(std::forward<Ts>(ts)...));
}

template <typename T, typename U>
bool operator==(
  const small_shared_ptrt<T> &lhs,
  const small_shared_ptrt<U> &rhs)
{
  return lhs.get() == rhs.get();
}

template <typename T, typename U>
bool operator!=(
  const small_shared_ptrt<T> &lhs,
  const small_shared_ptrt<U> &rhs)
{
  return lhs.get() != rhs.get();
}

template <typename T, typename U>
bool operator<(const small_shared_ptrt<T> &lhs, const small_shared_ptrt<U> &rhs)
{
  return lhs.get() < rhs.get();
}

template <typename T, typename U>
bool operator>(const small_shared_ptrt<T> &lhs, const small_shared_ptrt<U> &rhs)
{
  return lhs.get() > rhs.get();
}

template <typename T, typename U>
bool operator<=(
  const small_shared_ptrt<T> &lhs,
  const small_shared_ptrt<U> &rhs)
{
  return lhs.get() <= rhs.get();
}

template <typename T, typename U>
bool operator>=(
  const small_shared_ptrt<T> &lhs,
  const small_shared_ptrt<U> &rhs)
{
  return lhs.get() >= rhs.get();
}

////////////////////////////////////////////////////////////////////////////////

/// A helper class to store use-counts of objects held by small shared pointers.
/// The suggested usage pattern is to have such objects inherit
/// from this class, and then to access them through a small_shared_ptrt.
/// This approach provides us with shared_ptr-like semantics, but without the
/// space overhead required by shared_ptr. The idea is similar to
/// boost's intrusive_ptr.
/// \tparam Num some numeric type, used to store a reference count
template <typename Num>
class small_shared_pointeet
{
public:
  small_shared_pointeet() = default;

  // These can't be `= default` because we need the use_count_ to be unaffected
  small_shared_pointeet(const small_shared_pointeet &)
  {
  }
  small_shared_pointeet &operator=(const small_shared_pointeet &)
  {
    return *this;
  }
  small_shared_pointeet(small_shared_pointeet &&)
  {
  }
  small_shared_pointeet &operator=(small_shared_pointeet &&)
  {
    return *this;
  }

  void increment_use_count()
  {
    ++use_count_;
  }
  void decrement_use_count()
  {
    --use_count_;
  }
  Num use_count() const
  {
    return use_count_;
  }

protected:
  // Enables public inheritance but disables polymorphic usage
  ~small_shared_pointeet() = default;

private:
  Num use_count_ = 0;
};

/// The following functions are required by small_shared_ptrt, and by
/// default pass through to the member functions of small_shared_pointeet by the
/// same name. We provide these as non-members just in case a future client
/// wants to implement a shared object, which is unable to inherit from
/// small_shared_pointeet for some reason. In this case, new overloads for
/// the functions below can be provided, with appropriate behavior for the
/// new type.

template <typename Num>
inline void pointee_increment_use_count(small_shared_pointeet<Num> &p)
{
  p.increment_use_count();
}

template <typename Num>
inline void pointee_decrement_use_count(small_shared_pointeet<Num> &p)
{
  p.decrement_use_count();
}

template <typename Num>
inline Num pointee_use_count(const small_shared_pointeet<Num> &p)
{
  return p.use_count();
}

#endif
