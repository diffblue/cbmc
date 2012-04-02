/* FUNCTION: abs */

#undef abs

inline int abs(int i) { return __CPROVER_abs(i); }

/* FUNCTION: labs */

#undef labs

inline long int labs(long int i) { return __CPROVER_labs(i); }

/* FUNCTION: exit */

#undef exit

inline void exit(int status)
{
  __CPROVER_assume(0);
}

/* FUNCTION: abort */

#undef abort

inline void abort(void)
{
  __CPROVER_assume(0);
}

/* FUNCTION: calloc */

#undef calloc

inline void *calloc(__CPROVER_size_t nmemb, __CPROVER_size_t size)
{
  __CPROVER_HIDE:;
  __CPROVER_size_t total_size=nmemb*size;
  void *res;
  res=malloc(total_size);
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_is_zero_string(res);
  __CPROVER_zero_string_length(res)=0;
  //for(int i=0; i<nmemb*size; i++) res[i]=0;
  #else
  // there should be memset here
  //char *p=res;
  //for(int i=0; i<total_size; i++) p[i]=0;
  #endif
  return res;
}

/* FUNCTION: malloc */

inline void *malloc(__CPROVER_size_t malloc_size)
{
  // realistically, malloc may return NULL,
  // and __CPROVER_malloc doesn't, but no one cares
  __CPROVER_HIDE:;
  void *res;
  res=__CPROVER_malloc(malloc_size);

  // make sure it's not recorded as deallocated
  __CPROVER_deallocated=(res==__CPROVER_deallocated)?0:__CPROVER_deallocated;
  
  // record the object size for non-determistic bounds checking
  _Bool record_malloc;
  __CPROVER_malloc_object=record_malloc?res:__CPROVER_malloc_object;
  __CPROVER_malloc_size=record_malloc?malloc_size:__CPROVER_malloc_size;
  __CPROVER_malloc_is_new_array=record_malloc?0:__CPROVER_malloc_is_new_array;
  
  return res;
}

/* FUNCTION: free */

#undef free

inline void free(void *ptr)
{
  __CPROVER_HIDE:;
  // If ptr is NULL, no operation is performed.
  if(ptr!=0)
  {
    // is it dynamic?
    __CPROVER_assert(__CPROVER_DYNAMIC_OBJECT(ptr),
                     "free argument is dynamic object");
    __CPROVER_assert(__CPROVER_POINTER_OFFSET(ptr)==0,
                     "free argument has offset zero");

    // catch double free
    if(__CPROVER_deallocated==ptr)
      __CPROVER_assert(0, "double free");
      
    // catch people who try to use free(...) for stuff
    // allocated with new[]
    __CPROVER_assert(__CPROVER_malloc_object!=ptr ||
                     !__CPROVER_malloc_is_new_array,
                     "free called for new[] object");
    
    // non-deterministically record as deallocated
    _Bool record;
    if(record) __CPROVER_deallocated=ptr;
  }
}

/* FUNCTION: atoi */

#undef atoi

inline int atoi(const char *nptr)
{
  __CPROVER_HIDE:;
  int res;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(nptr),
    "zero-termination of argument of atoi");
  #endif
  return res;
}

/* FUNCTION: atol */

#undef atol

inline long atol(const char *nptr)
{
  __CPROVER_HIDE:;
  long res;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(nptr),
    "zero-termination of argument of atol");
  #endif
  return res;
}

/* FUNCTION: getenv */

#undef getenv

inline char *getenv(const char *name)
{
  __CPROVER_HIDE:;

  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(name),
    "zero-termination of argument of getenv");
  #endif

  _Bool found;
  if(!found) return 0;

  char *buffer;
  __CPROVER_size_t buf_size;

  __CPROVER_assume(buf_size>=1);
  buffer=(char *)__CPROVER_malloc(buf_size);
  buffer[buf_size-1]=0;
  return buffer;
}

/* FUNCTION: realloc */

inline void *realloc(void *ptr, __CPROVER_size_t malloc_size)
{
  __CPROVER_HIDE:;

  // if ptr is NULL, this behaves like malloc
  if(ptr==0)
    return malloc(malloc_size);

  // if malloc-size is 0, allocate new minimum sized object
  // and free original
  if(malloc_size==0)
  {
    free(ptr);
    return malloc(1);
  }

  __CPROVER_assert(__CPROVER_DYNAMIC_OBJECT(ptr),
                   "realloc argument is dynamic object");

  // this shouldn't move if the new size isn't bigger
  res=malloc(malloc_size);
  __CPROVER_array_copy(res, ptr);
  free(ptr);

  return res;
}

/* FUNCTION: valloc */

inline void *valloc(__CPROVER_size_t malloc_size)
{
  // The allocated memory is aligned on a page
  // boundary, which we don't model.
     
  __CPROVER_HIDE:;
  return malloc(malloc_size);
}
