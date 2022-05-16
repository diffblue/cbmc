/* FUNCTION: mmap */

#ifndef _WIN32

#  ifndef __CPROVER_SYS_MMAN_H_INCLUDED
#    include <sys/mman.h>
#    define __CPROVER_SYS_MMAN_H_INCLUDED
#  endif

#  ifndef MAP_FIXED
#    define MAP_FIXED 0
#  endif

#  ifndef MAP_ANONYMOUS
#    define MAP_ANONYMOUS 0
#  endif

#  ifndef MAP_UNINITIALIZED
#    define MAP_UNINITIALIZED 0
#  endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

void *mmap(
  void *addr,
  __CPROVER_size_t length,
  int prot,
  int flags,
  int fd,
  off_t offset)
{
  (void)prot;
  (void)fd;
  (void)offset;

  if(
    addr == 0 ||
    (__VERIFIER_nondet___CPROVER_bool() && (flags & MAP_FIXED) == 0))
  {
    if(flags & MAP_ANONYMOUS && (flags & MAP_UNINITIALIZED) == 0)
      return __CPROVER_allocate(length, 1);
    else
      return __CPROVER_allocate(length, 0);
  }
  else
  {
    __CPROVER_allocated_memory((__CPROVER_size_t)addr, length);
    return addr;
  }
}

#endif

/* FUNCTION: _mmap */

#ifndef _WIN32

#  ifndef __CPROVER_SYS_MMAN_H_INCLUDED
#    include <sys/mman.h>
#    define __CPROVER_SYS_MMAN_H_INCLUDED
#  endif

#  ifndef MAP_FIXED
#    define MAP_FIXED 0
#  endif

#  ifndef MAP_ANONYMOUS
#    define MAP_ANONYMOUS 0
#  endif

#  ifndef MAP_UNINITIALIZED
#    define MAP_UNINITIALIZED 0
#  endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

void *_mmap(
  void *addr,
  __CPROVER_size_t length,
  int prot,
  int flags,
  int fd,
  off_t offset)
{
  (void)prot;
  (void)fd;
  (void)offset;

  if(
    addr == 0 ||
    (__VERIFIER_nondet___CPROVER_bool() && (flags & MAP_FIXED) == 0))
  {
    if(flags & MAP_ANONYMOUS && (flags & MAP_UNINITIALIZED) == 0)
      return __CPROVER_allocate(length, 1);
    else
      return __CPROVER_allocate(length, 0);
  }
  else
  {
    __CPROVER_allocated_memory((__CPROVER_size_t)addr, length);
    return addr;
  }
}

#endif

/* FUNCTION: munmap */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

int munmap(void *addr, __CPROVER_size_t length)
{
  (void)length;

  __CPROVER_deallocate(addr);

  return 0;
}

/* FUNCTION: _munmap */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

int _munmap(void *addr, __CPROVER_size_t length)
{
  (void)length;

  __CPROVER_deallocate(addr);

  return 0;
}
