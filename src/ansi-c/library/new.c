/* FUNCTION: __new */

inline void *__new(__typeof__(sizeof(int)) malloc_size)
{
  // The constructor call is done by the front-end.
  // This just does memory allocation.
  __CPROVER_HIDE:;
  void *res;
  res=__CPROVER_malloc(malloc_size);

  // ensure it's not recorded as deallocated
  __CPROVER_deallocated=(res==__CPROVER_deallocated)?0:__CPROVER_deallocated;
  
  // non-derministically record the object size for bounds checking
  _Bool record_malloc;
  __CPROVER_malloc_object=record_malloc?res:__CPROVER_malloc_object;
  __CPROVER_malloc_size=record_malloc?malloc_size:__CPROVER_malloc_size;
  __CPROVER_malloc_is_new_array=record_malloc?0:__CPROVER_malloc_is_new_array;
  
  return res;
}

/* FUNCTION: __new_array */

#undef malloc
void *malloc(__CPROVER_size_t malloc_size);

inline void *__new_array(__CPROVER_size_t count, __CPROVER_size_t size)
{
  // The constructor call is done by the front-end.
  // This just does memory allocation.
  __CPROVER_HIDE:;
  void *res;
  res=__CPROVER_malloc(size*count);

  // ensure it's not recorded as deallocated
  __CPROVER_deallocated=(res==__CPROVER_deallocated)?0:__CPROVER_deallocated;
  
  // non-deterministically record the object size for bounds checking
  _Bool record_malloc;
  __CPROVER_malloc_object=record_malloc?res:__CPROVER_malloc_object;
  __CPROVER_malloc_size=record_malloc?size*count:__CPROVER_malloc_size;
  __CPROVER_malloc_is_new_array=record_malloc?1:__CPROVER_malloc_is_new_array;
  
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

inline void __delete(void *ptr)
{
  __CPROVER_HIDE:;
  // If ptr is NULL, no operation is performed.
  // This is a requirement by the standard, not generosity!
  if(ptr!=0)
  {
    // is it dynamic?
    __CPROVER_assert(__CPROVER_DYNAMIC_OBJECT(ptr),
                     "delete argument must be dynamic object");
    __CPROVER_assert(__CPROVER_POINTER_OFFSET(ptr)==0,
                     "delete argument must have offset zero");

    // catch double delete
    __CPROVER_assert(__CPROVER_deallocated!=ptr, "double delete");
    
    // catch people who call delete for objects allocated with new[]
    __CPROVER_assert(__CPROVER_malloc_object!=ptr ||
                     !__CPROVER_malloc_is_new_array,
                     "delete of array object");
    
    // non-deterministically record as deallocated
    _Bool record;
    __CPROVER_deallocated=record?ptr:__CPROVER_deallocated;
  }
}

/* FUNCTION: __delete_array */

inline void __delete_array(void *ptr)
{
  __CPROVER_HIDE:;
  // If ptr is NULL, no operation is performed.
  // This is a requirement by the standard, not generosity!
  if(ptr!=0)
  {
    // is it dynamic?
    __CPROVER_assert(__CPROVER_DYNAMIC_OBJECT(ptr),
                     "delete argument must be dynamic object");
    __CPROVER_assert(__CPROVER_POINTER_OFFSET(ptr)==0,
                     "delete argument must have offset zero");

    // catch double delete
    __CPROVER_assert(__CPROVER_deallocated!=ptr, "double delete");
    
    // catch people who call delete[] for objects allocated with new
    __CPROVER_assert(__CPROVER_malloc_object!=ptr ||
                     __CPROVER_malloc_is_new_array,
                     "delete[] of non-array object");

    // non-deterministically record as deallocated
    _Bool record;
    __CPROVER_deallocated=record?ptr:__CPROVER_deallocated;
  }
}

