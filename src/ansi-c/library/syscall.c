/* FUNCTION: syscall */

#ifndef __CPROVER_SYSCALL_H_INCLUDED
#  include <sys/syscall.h>
#  define __CPROVER_SYSCALL_H_INCLUDED
#endif

#ifndef __CPROVER_UNISTD_H_INCLUDED
#  include <unistd.h>
#  define __CPROVER_UNISTD_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_FCNTL_H_INCLUDED
#  include <fcntl.h>
#  define __CPROVER_FCNTL_H_INCLUDED
#endif

#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#  include <sys/types.h>
#  define __CPROVER_SYS_TYPES_H_INCLUDED
#endif

#include <stdarg.h>

// Forward declare the models we'll delegate to
int __CPROVER_open(const char *pathname, int flags);
int __CPROVER_creat(const char *pathname, mode_t mode);
int __CPROVER_openat(int dirfd, const char *pathname, int flags);
int __CPROVER_fcntl(int fd, int cmd);
int close(int fildes);
ssize_t read(int fildes, void *buf, size_t nbyte);
ssize_t write(int fildes, const void *buf, size_t nbyte);
int pipe(int fildes[2]);
int unlink(const char *s);

// Non-deterministic return values
long __VERIFIER_nondet_long(void);
int __VERIFIER_nondet_int(void);
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

// Main syscall function implementation
// Reference: https://github.com/diffblue/cbmc/issues/7646
// Implementation approach inspired by: https://github.com/model-checking/kani/issues/2284
//
// This model provides support for the syscall() function which is a generic
// system call interface. Where possible, it delegates to existing models for
// specific system calls. For unmodeled system calls, it provides a safe
// overapproximation by returning non-deterministic values with appropriate
// constraints.
long syscall(long number, ...)
{
  __CPROVER_HIDE:;
  va_list ap;
  va_start(ap, number);
  
  long result;

  // Delegate to existing models where available
  // System call numbers vary by architecture, but we handle common cases
  
#ifdef SYS_read
  if(number == SYS_read)
  {
    int fd = va_arg(ap, int);
    void *buf = va_arg(ap, void *);
    size_t count = va_arg(ap, size_t);
    result = (long)read(fd, buf, count);
    va_end(ap);
    return result;
  }
#endif

#ifdef SYS_write
  if(number == SYS_write)
  {
    int fd = va_arg(ap, int);
    const void *buf = va_arg(ap, const void *);
    size_t count = va_arg(ap, size_t);
    result = (long)write(fd, buf, count);
    va_end(ap);
    return result;
  }
#endif

#ifdef SYS_open
  if(number == SYS_open)
  {
    const char *pathname = va_arg(ap, const char *);
    int flags = va_arg(ap, int);
    // mode_t is optional, only used if O_CREAT is set
    result = (long)__CPROVER_open(pathname, flags);
    va_end(ap);
    return result;
  }
#endif

#ifdef SYS_close
  if(number == SYS_close)
  {
    int fd = va_arg(ap, int);
    result = (long)close(fd);
    va_end(ap);
    return result;
  }
#endif

#ifdef SYS_creat
  if(number == SYS_creat)
  {
    const char *pathname = va_arg(ap, const char *);
    mode_t mode = va_arg(ap, mode_t);
    result = (long)__CPROVER_creat(pathname, mode);
    va_end(ap);
    return result;
  }
#endif

#ifdef SYS_unlink
  if(number == SYS_unlink)
  {
    const char *pathname = va_arg(ap, const char *);
    result = (long)unlink(pathname);
    va_end(ap);
    return result;
  }
#endif

#ifdef SYS_pipe
  if(number == SYS_pipe)
  {
    int *pipefd = va_arg(ap, int *);
    result = (long)pipe(pipefd);
    va_end(ap);
    return result;
  }
#endif

#ifdef SYS_fcntl
  if(number == SYS_fcntl)
  {
    int fd = va_arg(ap, int);
    int cmd = va_arg(ap, int);
    result = (long)__CPROVER_fcntl(fd, cmd);
    va_end(ap);
    return result;
  }
#endif

#ifdef SYS_openat
  if(number == SYS_openat)
  {
    int dirfd = va_arg(ap, int);
    const char *pathname = va_arg(ap, const char *);
    int flags = va_arg(ap, int);
    result = (long)__CPROVER_openat(dirfd, pathname, flags);
    va_end(ap);
    return result;
  }
#endif

#ifdef SYS_dup
  if(number == SYS_dup)
  {
    // dup(oldfd) duplicates a file descriptor
    int oldfd = va_arg(ap, int);
    (void)oldfd; // Mark as used
    
    // Return non-deterministic file descriptor or error
    int retval = __VERIFIER_nondet_int();
    __CPROVER_assume(retval >= -1);
    
    if(retval == -1)
    {
      // Set errno to a valid error code for dup
      __CPROVER_bool emfile = __VERIFIER_nondet___CPROVER_bool();
      errno = emfile ? EMFILE : EBADF;
    }
    
    va_end(ap);
    return (long)retval;
  }
#endif

#ifdef SYS_dup2
  if(number == SYS_dup2)
  {
    // dup2(oldfd, newfd) duplicates a file descriptor to a specific fd
    int oldfd = va_arg(ap, int);
    int newfd = va_arg(ap, int);
    (void)oldfd; // Mark as used
    (void)newfd; // Mark as used
    
    // Return non-deterministic result
    int retval = __VERIFIER_nondet_int();
    __CPROVER_assume(retval >= -1);
    
    if(retval == -1)
    {
      __CPROVER_bool emfile = __VERIFIER_nondet___CPROVER_bool();
      errno = emfile ? EMFILE : EBADF;
    }
    
    va_end(ap);
    return (long)retval;
  }
#endif

#ifdef SYS_dup3
  if(number == SYS_dup3)
  {
    // dup3(oldfd, newfd, flags) is like dup2 but with flags
    int oldfd = va_arg(ap, int);
    int newfd = va_arg(ap, int);
    int flags = va_arg(ap, int);
    (void)oldfd; // Mark as used
    (void)newfd; // Mark as used
    (void)flags; // Mark as used
    
    int retval = __VERIFIER_nondet_int();
    __CPROVER_assume(retval >= -1);
    
    if(retval == -1)
    {
      errno = __VERIFIER_nondet_int();
    }
    
    va_end(ap);
    return (long)retval;
  }
#endif

#ifdef SYS_lseek
  if(number == SYS_lseek)
  {
    // lseek(fd, offset, whence) repositions file offset
    int fd = va_arg(ap, int);
    off_t offset = va_arg(ap, off_t);
    int whence = va_arg(ap, int);
    (void)fd;
    (void)offset;
    (void)whence;
    
    long retval = __VERIFIER_nondet_long();
    // lseek can return -1 on error or the resulting offset
    
    if(retval == -1)
    {
      // Common errno values: EBADF, EINVAL, ESPIPE
      errno = __VERIFIER_nondet_int();
    }
    
    va_end(ap);
    return retval;
  }
#endif

#ifdef SYS_getpid
  if(number == SYS_getpid)
  {
    // getpid() returns the process ID
    // Process IDs are positive integers
    int pid = __VERIFIER_nondet_int();
    __CPROVER_assume(pid > 0);
    va_end(ap);
    return (long)pid;
  }
#endif

#ifdef SYS_getuid
  if(number == SYS_getuid)
  {
    // getuid() returns the user ID
    // UIDs are non-negative
    int uid = __VERIFIER_nondet_int();
    __CPROVER_assume(uid >= 0);
    va_end(ap);
    return (long)uid;
  }
#endif

#ifdef SYS_getgid
  if(number == SYS_getgid)
  {
    // getgid() returns the group ID
    int gid = __VERIFIER_nondet_int();
    __CPROVER_assume(gid >= 0);
    va_end(ap);
    return (long)gid;
  }
#endif

#ifdef SYS_geteuid
  if(number == SYS_geteuid)
  {
    // geteuid() returns the effective user ID
    int euid = __VERIFIER_nondet_int();
    __CPROVER_assume(euid >= 0);
    va_end(ap);
    return (long)euid;
  }
#endif

#ifdef SYS_getegid
  if(number == SYS_getegid)
  {
    // getegid() returns the effective group ID
    int egid = __VERIFIER_nondet_int();
    __CPROVER_assume(egid >= 0);
    va_end(ap);
    return (long)egid;
  }
#endif

#ifdef SYS_gettid
  if(number == SYS_gettid)
  {
    // gettid() returns the thread ID
    int tid = __VERIFIER_nondet_int();
    __CPROVER_assume(tid > 0);
    va_end(ap);
    return (long)tid;
  }
#endif

  // For any unmodeled system call, return a non-deterministic value
  // This provides a safe overapproximation for verification purposes
  result = __VERIFIER_nondet_long();
  
  // Most system calls return -1 on error
  // We allow any return value but model potential error conditions
  __CPROVER_bool error = __VERIFIER_nondet___CPROVER_bool();
  if(error)
  {
    result = -1;
    // Set errno to a non-deterministic value representing possible errors
    errno = __VERIFIER_nondet_int();
    __CPROVER_assume(errno > 0); // errno values are positive
  }
  
  va_end(ap);
  return result;
}
