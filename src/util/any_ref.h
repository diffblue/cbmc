/*******************************************************************\

Module: Any reference - type-safe wrapper around void*

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_ANY_REF_H
#define CPROVER_UTIL_ANY_REF_H

#include <type_traits>
#include <typeinfo>

/// Any reference
/// Stores a reference to any type
/// Call .as<T>() to get the reference back
class any_reft final
{
public:
  template<typename T>
  explicit any_reft(T &val):
    type_(&type_of<T>),
    ptr_(const_cast<typename std::remove_const<T>::type *>(&val)) { }

  template<typename T>
  any_reft &operator=(T &val)
  {
    type_=&type_of<T>;
    ptr_=const_cast<typename std::remove_const<T>::type *>(&val);
    return *this;
  }

  template<typename T>
  bool operator==(const T &val) const
  {
    return
      (type_==&type_of<T> ||
       type_==&type_of<typename std::remove_const<T>::type>) &&
      *static_cast<T *>(ptr_)==val;
  }

  /// Convert to a reference of a specific type
  /// Throw std::bad_cast if type doesn't match the type
  template<typename T>
  T &as()
  {
    if(type_==&type_of<T> ||
       type_==&type_of<typename std::remove_const<T>::type>)
      return *static_cast<T *>(ptr_);
    throw std::bad_cast();
  }

  /// Convert to a reference of a specific type
  /// Throw std::bad_cast if type doesn't match the type
  template<typename T>
  const T &as() const
  {
    if(type_==&type_of<T> ||
       type_==&type_of<typename std::remove_const<T>::type>)
      return *static_cast<T *>(ptr_);
    throw std::bad_cast();
  }

private:
  template<typename T>
  static void type_of()
  {
#ifdef _WIN32
    // Hack to prevent VS release builds from optimizing this function out
    volatile int i=typeid(T).hash_code()+std::is_const<T>::value?1:0;
    (void)i;
#endif
  }

  void(*type_)();
  void *ptr_;
};

template<typename T>
bool operator==(const T& left, const any_reft &right)
{ return right==left; }

template<typename T>
bool operator!=(const any_reft &left, const T &right)
{ return !(left==right); }

template<typename T>
bool operator!=(const T &left, const any_reft &right)
{ return !(right==left); }

template<>
inline bool any_reft::operator==<any_reft>(const any_reft &other) const
{ return ptr_==other.ptr_ && type_==other.type_; }
#endif // CPROVER_UTIL_ANY_REF_H
