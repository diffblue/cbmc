/* FUNCTION: sleep */

unsigned __VERIFIER_nondet_unsigned();

unsigned int sleep(unsigned int seconds)
{
  __CPROVER_HIDE:;
  // do nothing, but return nondet value
  unsigned remaining_time=__VERIFIER_nondet_unsigned();

  if(remaining_time>seconds) remaining_time=seconds;

  return remaining_time;
}

/* FUNCTION: _sleep */

unsigned int sleep(unsigned int seconds);

inline unsigned int _sleep(unsigned int seconds)
{
  __CPROVER_HIDE:;
  return sleep(seconds);
}

/* FUNCTION: unlink */

int __VERIFIER_nondet_int();

int unlink(const char *s)
{
  __CPROVER_HIDE:;
  (void)*s;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s), "unlink zero-termination");
  #endif
  int retval=__VERIFIER_nondet_int();
  return retval;
}

/* FUNCTION: pipe */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#include <errno.h>
#define __CPROVER_ERRNO_H_INCLUDED
#endif

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;
extern unsigned __CPROVER_pipe_count;

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

int pipe(int fildes[2])
{
  __CPROVER_HIDE:;
  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  if(error)
  {
    errno=error==1 ? EMFILE : ENFILE;
    return -1;
  }

  __CPROVER_atomic_begin();
  __CPROVER_assume(__CPROVER_pipe_offset%2==0);
  __CPROVER_assume(__CPROVER_pipe_offset<=(int)(__CPROVER_pipe_offset+__CPROVER_pipe_count));
  fildes[0]=__CPROVER_pipe_offset+__CPROVER_pipe_count;
  fildes[1]=__CPROVER_pipe_offset+__CPROVER_pipe_count+1;
  __CPROVER_pipes[__CPROVER_pipe_count].widowed=0;
  __CPROVER_pipes[__CPROVER_pipe_count].next_avail=0;
  __CPROVER_pipes[__CPROVER_pipe_count].next_unread=0;
  __CPROVER_pipe_count+=2;
  __CPROVER_atomic_end();

  __CPROVER_assume(fildes[0]!=0 && fildes[0]!=1 && fildes[0]!=2);
  __CPROVER_assume(fildes[1]!=0 && fildes[1]!=1 && fildes[1]!=2);

  return 0;
}

/* FUNCTION: close */

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

int close(int fildes)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
    return 0;

  int retval=-1;
  fildes-=__CPROVER_pipe_offset;
  if(fildes%2==1)
    --fildes;
  __CPROVER_atomic_begin();
  if(!__CPROVER_pipes[fildes].widowed)
  {
    __CPROVER_pipes[fildes].widowed=1;
    __CPROVER_pipes[fildes].next_avail=__CPROVER_pipes[fildes].next_unread=0;
    retval=0;
  }
  __CPROVER_atomic_end();
  return retval;
}

/* FUNCTION: _close */

int close(int fildes);

inline int _close(int fildes)
{
  __CPROVER_HIDE:;
  return close(fildes);
}

/* FUNCTION: write */

// do not include unistd.h as this might trigger GCC asm renaming of
// write to _write; this is covered by the explicit definition of
// _write below
#ifdef _MSC_VER
#define ssize_t signed long
#else
#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif
#endif

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

ssize_t __VERIFIER_nondet_ssize_t();

ssize_t write(int fildes, const void *buf, size_t nbyte)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
  {
    ssize_t retval=__VERIFIER_nondet_ssize_t();
    __CPROVER_assume(retval>=-1 && retval<=(ssize_t)nbyte);
    return retval;
  }

  int retval=-1;
  fildes-=__CPROVER_pipe_offset;
  if(fildes%2==1)
    --fildes;
  __CPROVER_atomic_begin();
  if(!__CPROVER_pipes[fildes].widowed &&
      sizeof(__CPROVER_pipes[fildes].data) >=
      __CPROVER_pipes[fildes].next_avail+nbyte)
  {
    for(size_t i=0; i<nbyte; ++i)
      __CPROVER_pipes[fildes].data[i+__CPROVER_pipes[fildes].next_avail]=
        ((char*)buf)[i];
    __CPROVER_pipes[fildes].next_avail+=nbyte;
    retval=nbyte;
  }
  __CPROVER_atomic_end();
  return retval;
}

/* FUNCTION: _write */

#ifdef _MSC_VER
#define ssize_t signed long
#else
#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif
#endif

ssize_t write(int fildes, const void *buf, size_t nbyte);

inline ssize_t _write(int fildes, const void *buf, size_t nbyte)
{
  __CPROVER_HIDE:;
  return write(fildes, buf, nbyte);
}

/* FUNCTION: read */

// do not include unistd.h as this might trigger GCC asm renaming of
// read to _read; this is covered by the explicit definition of _read
// below
#ifdef _MSC_VER
#define ssize_t signed long
#else
#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif
#endif

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();
ssize_t __VERIFIER_nondet_ssize_t();

ssize_t read(int fildes, void *buf, size_t nbyte)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
  {
    ssize_t nread=__VERIFIER_nondet_ssize_t();
    __CPROVER_assume(0<=nread && (size_t)nread<=nbyte);

#if 0
    size_t i;
    for(i=0; i<nbyte; i++)
    {
      char nondet_char;
      ((char *)buf)[i]=nondet_char;
    }
#else
    char nondet_bytes[nbyte];
    __CPROVER_array_replace((char*)buf, nondet_bytes);
#endif

    __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
    return error ? -1 : nread;
  }

  int retval=0;
  fildes-=__CPROVER_pipe_offset;
  if(fildes%2==1)
    --fildes;
  __CPROVER_atomic_begin();
  if(!__CPROVER_pipes[fildes].widowed)
  {
    for(size_t i=0; i<nbyte &&
      __CPROVER_pipes[fildes].next_unread <
      __CPROVER_pipes[fildes].next_avail;
      ++i)
    {
      ((char*)buf)[i]=__CPROVER_pipes[fildes].
        data[__CPROVER_pipes[fildes].next_unread];
      ++__CPROVER_pipes[fildes].next_unread;
      ++retval;
    }
    if(__CPROVER_pipes[fildes].next_avail==
        __CPROVER_pipes[fildes].next_unread)
      __CPROVER_pipes[fildes].next_avail=__CPROVER_pipes[fildes].next_unread=0;
  }
  __CPROVER_atomic_end();
  return retval;
}

/* FUNCTION: _read */

#ifdef _MSC_VER
#define ssize_t signed long
#else
#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif
#endif

ssize_t read(int fildes, void *buf, size_t nbyte);

inline ssize_t _read(int fildes, void *buf, size_t nbyte)
{
  __CPROVER_HIDE:;
  return read(fildes, buf, nbyte);
}
