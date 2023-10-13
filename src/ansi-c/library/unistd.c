/* FUNCTION: sleep */

unsigned __VERIFIER_nondet_unsigned(void);

unsigned int sleep(unsigned int seconds)
{
  __CPROVER_HIDE:;
  // do nothing, but return nondet value
  unsigned remaining_time=__VERIFIER_nondet_unsigned();
  __CPROVER_assume(remaining_time <= seconds);

  return remaining_time;
}

/* FUNCTION: _sleep */

unsigned int sleep(unsigned int seconds);

unsigned int _sleep(unsigned int seconds)
{
  __CPROVER_HIDE:;
  return sleep(seconds);
}

/* FUNCTION: usleep */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

int usleep(unsigned int usec)
{
__CPROVER_HIDE:;
  // do nothing, but return nondet value
  __CPROVER_bool error = __VERIFIER_nondet___CPROVER_bool();
  if(error)
  {
    if(usec >= 1000000)
      errno = EINVAL;
    else
      errno = EINTR;
    return -1;
  }
  return 0;
}

/* FUNCTION: _usleep */

int usleep(unsigned int);

int _usleep(unsigned int usec)
{
__CPROVER_HIDE:;
  return usleep(usec);
}

/* FUNCTION: unlink */

int __VERIFIER_nondet_int(void);

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

extern struct __CPROVER_pipet __CPROVER_pipes[__CPROVER_constant_infinity_uint];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;
unsigned __CPROVER_pipe_count = 0;

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

int pipe(int fildes[2])
{
  __CPROVER_HIDE:;
  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  if(error)
  {
    errno = __VERIFIER_nondet___CPROVER_bool() ? EMFILE : ENFILE;
    return -1;
  }

  __CPROVER_atomic_begin();
  __CPROVER_assume(__CPROVER_pipe_offset >= 0);
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

extern struct __CPROVER_pipet __CPROVER_pipes[__CPROVER_constant_infinity_uint];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

int close(int fildes)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
    return 0;

  __CPROVER_assume(__CPROVER_pipe_offset >= 0);

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

int _close(int fildes)
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

extern struct __CPROVER_pipet __CPROVER_pipes[__CPROVER_constant_infinity_uint];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

ret_type __VERIFIER_nondet_ret_type(void);

ret_type write(int fildes, const void *buf, size_type nbyte)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
  {
    ret_type retval=__VERIFIER_nondet_ret_type();
    __CPROVER_assume(retval>=-1 && retval<=(ret_type)nbyte);
    return retval;
  }

  __CPROVER_assume(__CPROVER_pipe_offset >= 0);

  int retval=-1;
  fildes-=__CPROVER_pipe_offset;
  if(fildes%2==1)
    --fildes;
  __CPROVER_atomic_begin();
  if(
    !__CPROVER_pipes[fildes].widowed &&
    __CPROVER_pipes[fildes].next_avail >= 0 &&
    sizeof(__CPROVER_pipes[fildes].data) >=
      __CPROVER_pipes[fildes].next_avail + nbyte)
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

ret_type _write(int fildes, const void *buf, size_type nbyte)
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

extern struct __CPROVER_pipet __CPROVER_pipes[__CPROVER_constant_infinity_uint];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
ret_type __VERIFIER_nondet_ret_type(void);
size_type __VERIFIER_nondet_size_type(void);

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

  __CPROVER_assume(__CPROVER_pipe_offset >= 0);

  int retval=0;
  fildes-=__CPROVER_pipe_offset;
  if(fildes%2==1)
    --fildes;
  __CPROVER_atomic_begin();
  if(
    !__CPROVER_pipes[fildes].widowed &&
    __CPROVER_pipes[fildes].next_unread >= 0)
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

ret_type _read(int fildes, void *buf, size_type nbyte)
{
  __CPROVER_HIDE:;
  return read(fildes, buf, nbyte);
}

/* FUNCTION: sysconf */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

long __VERIFIER_nondet_long(void);
int __VERIFIER_nondet_int(void);

long sysconf(int name);

// This overapproximation is based on the sysconf specification available at
// https://pubs.opengroup.org/onlinepubs/9699919799/functions/sysconf.html.
long sysconf(int name)
{
__CPROVER_HIDE:;
  (void)name;
  long retval = __VERIFIER_nondet_long();

  // We should keep errno as non-deterministic as possible, since this model
  // never takes into account the name input.
  errno = __VERIFIER_nondet_int();

  // Spec states "some returned values may be huge; they are not suitable
  // for allocating memory". There aren't also guarantees about return
  // values being strictly equal or greater to -1.
  // Thus, modelling it as non-deterministic.
  return retval;
}

/* FUNCTION: syscall */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

long int __VERIFIER_nondet_long_int(void);
int __VERIFIER_nondet_int(void);

// This overapproximation is based on the syscall specification available at
// https://man7.org/linux/man-pages/man2/syscall.2.html and
// https://www.gnu.org/software/libc/manual/html_node/System-Calls.html.
//
// sysno is the system call number. The remaining arguments are the arguments
// for the system call. Each kind of system call has a definite number of
// arguments, from zero to five. If you code more arguments than the system
// call takes, the extra ones to the right are ignored.
#ifdef __APPLE__
int syscall(int sysno, ...);
int syscall(int sysno, ...)
#else
long int syscall(long int sysno, ...);
long int syscall(long int sysno, ...)
#endif
{
__CPROVER_HIDE:;
  (void)sysno;

#ifdef __APPLE__
  int retval = __VERIFIER_nondet_int();
#else
  long int retval = __VERIFIER_nondet_long_int();
#endif

  if(retval == -1)
  {
    // We should keep errno as non-deterministic as possible, since this model
    // never takes into account any input.
    errno = __VERIFIER_nondet_int();
  }

  // The return value is the return value from the system call, unless the
  // system call failed. This over-approximation doesn't take into account
  // any system call operation, so we leave the return value as non-det.
  return retval;
}
