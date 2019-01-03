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
  __CPROVER_precondition(__CPROVER_is_zero_string(s),
                         "unlink zero-termination");
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

/* FUNCTION: _pipe */

#ifdef _WIN32
#undef pipe
int pipe(int fildes[2]);

int _pipe(int *pfds, unsigned int psize, int textmode)
{
__CPROVER_HIDE:;
  (void)psize;
  (void)textmode;
  return pipe(pfds);
}
#endif

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
#define ret_type int
#define size_type unsigned
#else
#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif
#define ret_type ssize_t
#define size_type size_t
#endif

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

ret_type __VERIFIER_nondet_ret_type();

ret_type write(int fildes, const void *buf, size_type nbyte)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
  {
    ret_type retval=__VERIFIER_nondet_ret_type();
    __CPROVER_assume(retval>=-1 && retval<=(ret_type)nbyte);
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
    for(size_type i=0; i<nbyte; ++i)
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
#define ret_type int
#define size_type unsigned
#else
#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif
#define ret_type ssize_t
#define size_type size_t
#endif

ret_type write(int fildes, const void *buf, size_type nbyte);

inline ret_type _write(int fildes, const void *buf, size_type nbyte)
{
  __CPROVER_HIDE:;
  return write(fildes, buf, nbyte);
}

/* FUNCTION: read */

// do not include unistd.h as this might trigger GCC asm renaming of
// read to _read; this is covered by the explicit definition of _read
// below
#ifdef _MSC_VER
#define ret_type int
#define size_type unsigned
#else
#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif
#define ret_type ssize_t
#define size_type size_t
#endif

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();
ret_type __VERIFIER_nondet_ret_type();
size_type __VERIFIER_nondet_size_type();

ret_type read(int fildes, void *buf, size_type nbyte)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
  {
    ret_type nread=__VERIFIER_nondet_ret_type();
    __CPROVER_assume(0<=nread && (size_type)nread<=nbyte);

    __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
#if 0
    size_type i;
    for(i=0; i<nbyte; i++)
    {
      char nondet_char;
      ((char *)buf)[i]=nondet_char;
    }
#else
    if(nbyte>0)
    {
      size_type str_length=__VERIFIER_nondet_size_type();
      __CPROVER_assume(error ? str_length<=nbyte : str_length==nbyte);
      // check that the memory is accessible
      (void)*(char *)buf;
      (void)*(((const char *)buf) + str_length - 1);
      char contents_nondet[str_length];
      __CPROVER_array_replace((char*)buf, contents_nondet);
    }
#endif

    return error ? -1 : nread;
  }

  int retval=0;
  fildes-=__CPROVER_pipe_offset;
  if(fildes%2==1)
    --fildes;
  __CPROVER_atomic_begin();
  if(!__CPROVER_pipes[fildes].widowed)
  {
    for(size_type i=0; i<nbyte &&
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
#define ret_type int
#define size_type unsigned
#else
#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif
#define ret_type ssize_t
#define size_type size_t
#endif

ret_type read(int fildes, void *buf, size_type nbyte);

inline ret_type _read(int fildes, void *buf, size_type nbyte)
{
  __CPROVER_HIDE:;
  return read(fildes, buf, nbyte);
}
