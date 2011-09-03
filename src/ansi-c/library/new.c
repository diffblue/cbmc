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
  
  // record the object size for non-determistic bounds checking
  _Bool record_malloc;
  if(record_malloc)
  {
    __CPROVER_malloc_object=res;
    __CPROVER_malloc_size=malloc_size;
  }
  
  return res;
}

/* FUNCTION: __placement_new */

inline void *__placement_new(__typeof__(sizeof(int)) malloc_size, void *p)
{
  // The constructor call is done by the front-end.
  __CPROVER_HIDE:;
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
    
    // non-deterministically record as deallocated
    __CPROVER_deallocated=record?ptr:__CPROVER_deallocated;
  }
}

