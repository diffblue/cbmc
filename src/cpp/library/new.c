/* FUNCTION: __new */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline void *__new(__typeof__(sizeof(int)) malloc_size)
{
  // The constructor call is done by the front-end.
  // This just does memory allocation.
  __CPROVER_HIDE:;
  void *res;
  res = __CPROVER_allocate(malloc_size, 0);

  // ensure it's not recorded as deallocated
  __CPROVER_deallocated=(res==__CPROVER_deallocated)?0:__CPROVER_deallocated;

  // non-deterministically record the object for delete/delete[] checking
  __CPROVER_bool record_malloc=__VERIFIER_nondet___CPROVER_bool();
  __CPROVER_new_object = record_malloc ? res : __CPROVER_new_object;
  __CPROVER_malloc_is_new_array=record_malloc?0:__CPROVER_malloc_is_new_array;

  // detect memory leaks
  __CPROVER_bool record_may_leak=__VERIFIER_nondet___CPROVER_bool();
  __CPROVER_memory_leak=record_may_leak?res:__CPROVER_memory_leak;

  return res;
}

/* FUNCTION: __new_array */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline void *__new_array(__CPROVER_size_t count, __CPROVER_size_t size)
{
  // The constructor call is done by the front-end.
  // This just does memory allocation.
  __CPROVER_HIDE:;
  void *res;
  res = __CPROVER_allocate(size*count, 0);

  // ensure it's not recorded as deallocated
  __CPROVER_deallocated=(res==__CPROVER_deallocated)?0:__CPROVER_deallocated;

  // non-deterministically record the object for delete/delete[] checking
  __CPROVER_bool record_malloc=__VERIFIER_nondet___CPROVER_bool();
  __CPROVER_new_object = record_malloc ? res : __CPROVER_new_object;
  __CPROVER_malloc_is_new_array=record_malloc?1:__CPROVER_malloc_is_new_array;

  // detect memory leaks
  __CPROVER_bool record_may_leak=__VERIFIER_nondet___CPROVER_bool();
  __CPROVER_memory_leak=record_may_leak?res:__CPROVER_memory_leak;

  return res;
}

/* FUNCTION: __placement_new */

inline void *__placement_new(__typeof__(sizeof(int)) malloc_size, void *p)
{
  // The constructor call is done by the front-end.
  // The allocation is done by the user. So this does nothing.
  __CPROVER_HIDE:;
  (void)malloc_size;
  return p;
}

/* FUNCTION: __delete */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline void __delete(void *ptr)
{
  __CPROVER_HIDE:;
  // is it dynamic?
  __CPROVER_precondition(ptr==0 || __CPROVER_DYNAMIC_OBJECT(ptr),
                         "delete argument must be dynamic object");
  __CPROVER_precondition(__CPROVER_POINTER_OFFSET(ptr)==0,
                         "delete argument must have offset zero");

  // catch double delete
  __CPROVER_precondition(ptr==0 || __CPROVER_deallocated!=ptr, "double delete");

  // catch people who call delete for objects allocated with new[]
  __CPROVER_precondition(
    ptr == 0 || __CPROVER_new_object != ptr || !__CPROVER_malloc_is_new_array,
    "delete of array object");

  // If ptr is NULL, no operation is performed.
  // This is a requirement by the standard, not generosity!
  if(ptr!=0)
  {
    __CPROVER_deallocate(ptr);

    // detect memory leaks
    if(__CPROVER_memory_leak==ptr)
      __CPROVER_memory_leak=0;
  }
}

/* FUNCTION: __delete_array */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline void __delete_array(void *ptr)
{
  __CPROVER_HIDE:;
  // If ptr is NULL, no operation is performed.
  // This is a requirement by the standard, not generosity!

  // is it dynamic?
  __CPROVER_precondition(ptr==0 || __CPROVER_DYNAMIC_OBJECT(ptr),
                         "delete argument must be dynamic object");
  __CPROVER_precondition(ptr==0 || __CPROVER_POINTER_OFFSET(ptr)==0,
                         "delete argument must have offset zero");

  // catch double delete
  __CPROVER_precondition(ptr==0 || __CPROVER_deallocated!=ptr,
                         "double delete");

  // catch people who call delete[] for objects allocated with new
  __CPROVER_precondition(
    ptr == 0 || __CPROVER_new_object != ptr || __CPROVER_malloc_is_new_array,
    "delete[] of non-array object");

  if(ptr!=0)
  {
    __CPROVER_deallocate(ptr);

    // detect memory leaks
    if(__CPROVER_memory_leak==ptr) __CPROVER_memory_leak=0;
  }
}
