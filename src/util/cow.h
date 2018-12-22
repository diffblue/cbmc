/*******************************************************************\

Module: Copy on write class

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_COW_H
#define CPROVER_UTIL_COW_H

#include "invariant.h"
#include "small_shared_ptr.h"

#include <limits>

/// A utility class for writing types with copy-on-write behaviour (like irep).
/// This is a thin wrapper over a shared pointer, but instead of a single
/// getter for the pointer value, we supply a separate 'read' and 'write'
/// method. 'read' returns a reference to the owned object, while 'write'
/// will create a copy of the owned object if more than one copy_on_write
/// instance points to it.
template <typename T>
class copy_on_writet final
{
public:
  // Note that this *is* the default constructor. An invariant of a
  // copy-on-write object is that it is never null.
  template <typename... Ts>
  explicit copy_on_writet(Ts &&... ts)
    : t_(make_small_shared_ptr<T>(std::forward<Ts>(ts)...))
  {
    INVARIANT(
      pointee_is_shareable(*t_),
      "newly-constructed COW pointers must be shareable");
  }

  copy_on_writet(const copy_on_writet &rhs)
    : t_(
        pointee_is_shareable(*rhs.t_) ? rhs.t_
                                      : make_small_shared_ptr<T>(*rhs.t_))
  {
    INVARIANT(
      pointee_is_shareable(*t_),
      "newly-constructed COW pointers must be shareable");
  }

  copy_on_writet &operator=(const copy_on_writet &rhs)
  {
    auto copy(rhs);
    swap(copy);
    return *this;
  }

  copy_on_writet(copy_on_writet &&rhs)
  {
    swap(rhs);
  }

  copy_on_writet &operator=(copy_on_writet &&rhs)
  {
    swap(rhs);
    return *this;
  }

  void swap(copy_on_writet &rhs)
  {
    std::swap(t_, rhs.t_);
  }

  const T &read() const
  {
    return *t_;
  }

  T &write(bool mark_shareable)
  {
    if(pointee_use_count(*t_) != 1)
    {
      t_ = make_small_shared_ptr<T>(*t_);
    }
    INVARIANT(
      pointee_use_count(*t_) == 1,
      "mutable references to a COW pointer must be unique");
    pointee_set_shareable(*t_, mark_shareable);
    return *t_;
  }

  // Ideally these would be non-members, but they depend on private member t_

  template <typename U>
  bool operator==(const copy_on_writet<U> &rhs) const
  {
    return t_ == rhs.t_;
  }

  template <typename U>
  bool operator!=(const copy_on_writet<U> &rhs) const
  {
    return t_ != rhs.t_;
  }

  template <typename U>
  bool operator<(const copy_on_writet<U> &rhs) const
  {
    return t_ < rhs.t_;
  }

  template <typename U>
  bool operator>(const copy_on_writet<U> &rhs) const
  {
    return t_ > rhs.t_;
  }

  template <typename U>
  bool operator<=(const copy_on_writet<U> &rhs) const
  {
    return t_ <= rhs.t_;
  }

  template <typename U>
  bool operator>=(const copy_on_writet<U> &rhs) const
  {
    return t_ >= rhs.t_;
  }

private:
  small_shared_ptrt<T> t_;
};

////////////////////////////////////////////////////////////////////////////////

/// A helper class to store use-counts of copy-on-write objects.
/// The suggested usage pattern is to have copy-on-write data types inherit
/// from this class, and then to access them through a copy_on_writet.
/// \tparam Num: some numeric type, used to store a reference count
template <typename Num>
class copy_on_write_pointeet
{
public:
  copy_on_write_pointeet() = default;

  copy_on_write_pointeet(const copy_on_write_pointeet &)
  {
  }

  copy_on_write_pointeet &operator=(const copy_on_write_pointeet &)
  {
    return *this;
  }

  copy_on_write_pointeet(copy_on_write_pointeet &&)
  {
  }

  copy_on_write_pointeet &operator=(copy_on_write_pointeet &&)
  {
    return *this;
  }

  void increment_use_count()
  {
    INVARIANT(
      is_shareable(),
      "cannot increment the use count of a non-shareable reference");
    ++use_count_;
  }

  void decrement_use_count()
  {
    INVARIANT(
      is_shareable(),
      "cannot decrement the use count of a non-shareable reference");
    --use_count_;
  }

  Num use_count() const
  {
    return is_shareable() ? use_count_ : 1;
  }

  void set_shareable(bool u)
  {
    use_count_ = u ? 1 : unshareable;
  }

  bool is_shareable() const
  {
    return use_count_ != unshareable;
  }

protected:
  ~copy_on_write_pointeet() = default;

private:
  /// A special sentry value which will be assigned to use_count_ if
  /// a mutable reference to the held object has been created. We check for
  /// this sentry value, and use it to decide whether the next copy
  /// constructor/assignment call should invoke a deep or shallow copy.
  /// Note that this is set to the max value that can be held by Num, but
  /// this cannot be done inline.
  static const Num unshareable;
  Num use_count_ = 0;
};

template <typename Num>
const Num copy_on_write_pointeet<Num>::unshareable =
  (std::numeric_limits<Num>::max)(); // suppress macro expansion on windows

/// The following functions are required by copy_on_writet, and by default pass
/// through to the member functions of copy_on_write_pointeet by the same name.
/// We provide these as non-members just in case a future client wants to
/// implement a copy-on-write class, which is unable to inherit from
/// copy_on_write_pointeet for some reason. In this case, new overloads for
/// the functions below can be provided, with appropriate behavior for the new
/// type.

template <typename Num>
inline void pointee_increment_use_count(copy_on_write_pointeet<Num> &p)
{
  p.increment_use_count();
}

template <typename Num>
inline void pointee_decrement_use_count(copy_on_write_pointeet<Num> &p)
{
  p.decrement_use_count();
}

template <typename Num>
inline Num pointee_use_count(const copy_on_write_pointeet<Num> &p)
{
  return p.use_count();
}

template <typename Num, typename T>
inline void pointee_set_use_count(copy_on_write_pointeet<Num> &p, T count)
{
  p.set_use_count(count);
}

template <typename Num>
inline void pointee_set_shareable(copy_on_write_pointeet<Num> &p, bool u)
{
  p.set_shareable(u);
}

template <typename Num>
inline bool pointee_is_shareable(const copy_on_write_pointeet<Num> &p)
{
  return p.is_shareable();
}

#endif
