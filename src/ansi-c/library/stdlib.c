/* FUNCTION: abs */

#undef abs

inline int abs(int i) { return __CPROVER_abs(i); }

/* FUNCTION: labs */

#undef labs

inline long int labs(long int i) { return __CPROVER_labs(i); }

/* FUNCTION: llabs */

#undef llabs

inline long long int llabs(long long int i) { return __CPROVER_llabs(i); }

/* FUNCTION: __builtin_abs */

inline int __builtin_abs(int i) { return __CPROVER_abs(i); }

/* FUNCTION: __builtin_labs */

inline long int __builtin_labs(long int i) { return __CPROVER_labs(i); }

/* FUNCTION: __builtin_llabs */

inline long long int __builtin_llabs(long long int i) { return __CPROVER_llabs(i); }

/* FUNCTION: exit */

#undef exit

inline void exit(int status)
{
  (void)status;
  __CPROVER_assume(0);
}

/* FUNCTION: _Exit */

#undef _Exit

inline void _Exit(int status)
{
  (void)status;
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

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline void *calloc(__CPROVER_size_t nmemb, __CPROVER_size_t size)
{
  // realistically, calloc may return NULL,
  // and __CPROVER_allocate doesn't, but no one cares
  __CPROVER_HIDE:;
  void *malloc_res;
  malloc_res = __CPROVER_allocate(nmemb * size, 1);

  // make sure it's not recorded as deallocated
  __CPROVER_deallocated =
    (malloc_res == __CPROVER_deallocated) ? 0 : __CPROVER_deallocated;

  // record the object size for non-determistic bounds checking
  __CPROVER_bool record_malloc = __VERIFIER_nondet___CPROVER_bool();
  __CPROVER_malloc_object =
    record_malloc ? malloc_res : __CPROVER_malloc_object;
  __CPROVER_malloc_size = record_malloc ? nmemb * size : __CPROVER_malloc_size;
  __CPROVER_malloc_is_new_array =
    record_malloc ? 0 : __CPROVER_malloc_is_new_array;

  // detect memory leaks
  __CPROVER_bool record_may_leak = __VERIFIER_nondet___CPROVER_bool();
  __CPROVER_memory_leak = record_may_leak ? malloc_res : __CPROVER_memory_leak;

#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_is_zero_string(malloc_res) = 1;
  __CPROVER_zero_string_length(malloc_res) = 0;
#endif

  return malloc_res;
}

/* FUNCTION: malloc */

#undef malloc

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline void *malloc(__CPROVER_size_t malloc_size)
{
  // realistically, malloc may return NULL,
  // and __CPROVER_allocate doesn't, but no one cares
  __CPROVER_HIDE:;
  void *malloc_res;
  malloc_res = __CPROVER_allocate(malloc_size, 0);

  // make sure it's not recorded as deallocated
  __CPROVER_deallocated=(malloc_res==__CPROVER_deallocated)?0:__CPROVER_deallocated;

  // record the object size for non-determistic bounds checking
  __CPROVER_bool record_malloc=__VERIFIER_nondet___CPROVER_bool();
  __CPROVER_malloc_object=record_malloc?malloc_res:__CPROVER_malloc_object;
  __CPROVER_malloc_size=record_malloc?malloc_size:__CPROVER_malloc_size;
  __CPROVER_malloc_is_new_array=record_malloc?0:__CPROVER_malloc_is_new_array;

  // detect memory leaks
  __CPROVER_bool record_may_leak=__VERIFIER_nondet___CPROVER_bool();
  __CPROVER_memory_leak=record_may_leak?malloc_res:__CPROVER_memory_leak;

  return malloc_res;
}

/* FUNCTION: __builtin_alloca */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline void *__builtin_alloca(__CPROVER_size_t alloca_size)
{
  __CPROVER_HIDE:;
  void *res;
  res = __CPROVER_allocate(alloca_size, 0);

  // make sure it's not recorded as deallocated
  __CPROVER_deallocated=(res==__CPROVER_deallocated)?0:__CPROVER_deallocated;

  // record the object size for non-determistic bounds checking
  __CPROVER_bool record_malloc=__VERIFIER_nondet___CPROVER_bool();
  __CPROVER_malloc_object=record_malloc?res:__CPROVER_malloc_object;
  __CPROVER_malloc_size=record_malloc?alloca_size:__CPROVER_malloc_size;
  __CPROVER_malloc_is_new_array=record_malloc?0:__CPROVER_malloc_is_new_array;

  return res;
}

/* FUNCTION: free */

#undef free

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline void free(void *ptr)
{
  __CPROVER_HIDE:;
  // If ptr is NULL, no operation is performed.
  __CPROVER_precondition(ptr==0 || __CPROVER_DYNAMIC_OBJECT(ptr),
                         "free argument must be dynamic object");
  __CPROVER_precondition(ptr==0 || __CPROVER_POINTER_OFFSET(ptr)==0,
                         "free argument has offset zero");

  // catch double free
  __CPROVER_precondition(ptr==0 || __CPROVER_deallocated!=ptr,
                         "double free");

  // catch people who try to use free(...) for stuff
  // allocated with new[]
  __CPROVER_precondition(ptr==0 ||
                         __CPROVER_malloc_object!=ptr ||
                         !__CPROVER_malloc_is_new_array,
                         "free called for new[] object");

  if(ptr!=0)
  {
    // non-deterministically record as deallocated
    __CPROVER_bool record=__VERIFIER_nondet___CPROVER_bool();
    if(record) __CPROVER_deallocated=ptr;

    // detect memory leaks
    if(__CPROVER_memory_leak==ptr)
      __CPROVER_memory_leak=0;
  }
}

/* FUNCTION: strtol */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#include <errno.h>
#define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_LIMITS_H_INCLUDED
#include <limits.h>
#define __CPROVER_LIMITS_H_INCLUDED
#endif

#undef strtol
#undef isdigit
#undef isspace

int isspace(int);
int isdigit(int);

inline long strtol(const char *nptr, char **endptr, int base)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(nptr),
    "zero-termination of argument of strtol");
  #endif

  if(base==1 || base<0 || base>36)
  {
    errno=EINVAL;
    return 0;
  }

  long res=0;
  _Bool in_number=0;
  char sign=0;

  // 32 chars is an arbitrarily chosen limit
  int i=0;
  for( ; i<31; ++i)
  {
    char ch=nptr[i];
    char sub=0;
    if(ch==0)
      break;
    else if((base==0 || base==16) && !in_number &&
            ch=='0' && (nptr[i+1]=='x' || nptr[i+1]=='X'))
    {
      base=16;
      in_number=1;
      ++i;
      continue;
    }
    else if(base==0 && !in_number && ch=='0')
    {
      base=8;
      in_number=1;
      continue;
    }
    else if(!in_number && !sign && isspace(ch))
      continue;
    else if(!in_number && !sign && (ch=='-' || ch=='+'))
    {
      sign=ch;
      continue;
    }
    else if(base>10 && ch>='a' && ch-'a'<base-10)
      sub='a'-10;
    else if(base>10 && ch>='A' && ch-'A'<base-10)
      sub='A'-10;
    else if(isdigit(ch))
    {
      sub='0';
      base=base==0 ? 10 : base;
    }
    else
      break;

    in_number=1;
    long res_before=res;
    res=res*base+ch-sub;
    if(res<res_before)
    {
      errno=ERANGE;
      if(sign=='-')
        return LONG_MIN;
      else
        return LONG_MAX;
    }
  }

  if(endptr!=0)
    *endptr=(char*)nptr+i;

  if(sign=='-')
    res*=-1;

  return res;
}

/* FUNCTION: atoi */

#undef atoi
#undef strtol

long strtol(const char *nptr, char **endptr, int base);

inline int atoi(const char *nptr)
{
  __CPROVER_HIDE:;
  return (int)strtol(nptr, (char **)0, 10);
}

/* FUNCTION: atol */

#undef atol
#undef strtol

long strtol(const char *nptr, char **endptr, int base);

inline long atol(const char *nptr)
{
  __CPROVER_HIDE:;
  return strtol(nptr, (char **)0, 10);
}

/* FUNCTION: getenv */

#undef getenv

#ifndef __CPROVER_LIMITS_H_INCLUDED
#include <limits.h>
#define __CPROVER_LIMITS_H_INCLUDED
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();
__CPROVER_size_t __VERIFIER_nondet___CPROVER_size_t();

inline void *__builtin_alloca(__CPROVER_size_t alloca_size);

inline char *getenv(const char *name)
{
  __CPROVER_HIDE:;

  (void)*name;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(name),
    "zero-termination of argument of getenv");
  #endif

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "getenv_result");
  char *getenv_result;
  __CPROVER_set_must(getenv_result, "getenv_result");
  return getenv_result;

  #else

  __CPROVER_bool found=__VERIFIER_nondet___CPROVER_bool();
  if(!found) return 0;

  __CPROVER_size_t buf_size=__VERIFIER_nondet___CPROVER_size_t();

  // It's reasonable to assume this won't exceed the signed
  // range in practice, but in principle, this could exceed
  // the range.

  __CPROVER_assume(1<=buf_size && buf_size<=SSIZE_MAX);
  char *buffer=(char *)__builtin_alloca(buf_size);
  buffer[buf_size-1]=0;

  return buffer;
  #endif
}

/* FUNCTION: realloc */

inline void *malloc(__CPROVER_size_t malloc_size);
inline void free(void *ptr);

inline void *realloc(void *ptr, __CPROVER_size_t malloc_size)
{
  __CPROVER_HIDE:;

  __CPROVER_precondition(ptr==0 || __CPROVER_DYNAMIC_OBJECT(ptr),
                         "realloc argument is dynamic object");

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

  // this shouldn't move if the new size isn't bigger
  void *res;
  res=malloc(malloc_size);
  __CPROVER_array_copy(res, ptr);
  free(ptr);

  return res;
}

/* FUNCTION: valloc */

inline void *malloc(__CPROVER_size_t malloc_size);

inline void *valloc(__CPROVER_size_t malloc_size)
{
  // The allocated memory is aligned on a page
  // boundary, which we don't model.

  __CPROVER_HIDE:;
  return malloc(malloc_size);
}

/* FUNCTION: posix_memalign */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#include <errno.h>
#define __CPROVER_ERRNO_H_INCLUDED
#endif

#undef posix_memalign

inline void *malloc(__CPROVER_size_t malloc_size);
inline int
posix_memalign(void **ptr, __CPROVER_size_t alignment, __CPROVER_size_t size)
{
__CPROVER_HIDE:;

  __CPROVER_size_t multiplier = alignment / sizeof(void *);
  // Modeling the posix_memalign checks on alignment.
  if(
    alignment % sizeof(void *) != 0 || ((multiplier) & (multiplier - 1)) != 0 ||
    alignment == 0)
  {
    return EINVAL;
  }
  // The address of the allocated memory is supposed to be aligned with
  // alignment. As cbmc doesn't model address alignment,
  // assuming MALLOC_ALIGNMENT = MAX_INT_VALUE seems fair.
  // As _mid_memalign simplifies for alignment <= MALLOC_ALIGNMENT
  // to a malloc call, it should be sound, if we do it too.

  // The original posix_memalign check on the pointer is:

  // void *tmp = malloc(size);
  // if(tmp != NULL){
  //   *ptr = tmp;
  //   return 0;
  // }
  // return ENOMEM;

  // As _CPROVER_allocate used in malloc never returns null,
  // this check is not applicable and can be simplified:

  *ptr = malloc(size);
  return 0;
}

/* FUNCTION: random */

long __VERIFIER_nondet_long();

long random(void)
{
  // We return a non-deterministic value instead of a random one.
  __CPROVER_HIDE:;
  long result=__VERIFIER_nondet_long();
  __CPROVER_assume(result>=0 && result<=2147483647);
  return result;
}
