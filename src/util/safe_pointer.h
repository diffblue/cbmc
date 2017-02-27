/*******************************************************************\

Module: Simple checked pointers

Author: Chris Smowton, chris@smowton.net

\*******************************************************************/

#ifndef CPROVER_UTIL_SAFE_POINTER_H
#define CPROVER_UTIL_SAFE_POINTER_H

template<class T> class safe_pointer
{
 public:
  operator bool() const
  {
    return !!ptr;
  }

  T *get() const
  {
    assert(ptr && "dereferenced a null safe pointer");
    return ptr;
  }

  T &operator*() const
  {
    return *get();
  }

  T *operator->() const
  {
    return get();
  }

  static safe_pointer<T> create_null()
  {
    return safe_pointer();
  }

  static safe_pointer<T> create_non_null(
    T *target)
  {
    assert(target && "initialized safe pointer with null");
    return safe_pointer(target);
  }

  static safe_pointer<T> create_maybe_null(
    T *target)
  {
    return safe_pointer(target);
  }

 protected:
  T *ptr;

  explicit safe_pointer(T *target) : ptr(target)
  {}

  safe_pointer() : ptr(nullptr)
  {}
};

#endif
