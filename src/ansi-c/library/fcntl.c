/* FUNCTION: __CPROVER_fcntl */

#ifndef __CPROVER_FCNTL_H_INCLUDED
#include <fcntl.h>
#define __CPROVER_FCNTL_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int __CPROVER_fcntl(int fd, int cmd)
{
__CPROVER_HIDE:;
  if(fd < 0)
  {
    errno = EBADF;
    return -1;
  }

  int return_value=__VERIFIER_nondet_int();
  (void)fd;
  (void)cmd;
  return return_value;
}

/* FUNCTION: fcntl */

int __CPROVER_fcntl(int, int);

int fcntl(int fd, int cmd, ...)
{
  return __CPROVER_fcntl(fd, cmd);
}

/* FUNCTION: _fcntl */

int __CPROVER_fcntl(int, int);

int _fcntl(int fd, int cmd, ...)
{
  return __CPROVER_fcntl(fd, cmd);
}

/* FUNCTION: fcntl64 */

int __CPROVER_fcntl(int, int);

int fcntl64(int fd, int cmd, ...)
{
  return __CPROVER_fcntl(fd, cmd);
}

/* FUNCTION: __fcntl_time64 */

int __CPROVER_fcntl(int, int);

int __fcntl_time64(int fd, int cmd, ...)
{
  return __CPROVER_fcntl(fd, cmd);
}

/* FUNCTION: __CPROVER_open */

#ifndef __CPROVER_FCNTL_H_INCLUDED
#  include <fcntl.h>
#  define __CPROVER_FCNTL_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int __CPROVER_open(const char *pathname, int flags)
{
__CPROVER_HIDE:;
  int return_value = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value >= -1);
  (void)*pathname;
  (void)flags;
  return return_value;
}

/* FUNCTION: open */

int __CPROVER_open(const char *, int);

int open(const char *pathname, int flags, ...)
{
  return __CPROVER_open(pathname, flags);
}

/* FUNCTION: _open */

int __CPROVER_open(const char *, int);

int _open(const char *pathname, int flags, ...)
{
  return __CPROVER_open(pathname, flags);
}

/* FUNCTION: open64 */

int __CPROVER_open(const char *, int);

int open64(const char *pathname, int flags, ...)
{
  return __CPROVER_open(pathname, flags);
}

/* FUNCTION: __CPROVER_creat */

#ifndef __CPROVER_FCNTL_H_INCLUDED
#  include <fcntl.h>
#  define __CPROVER_FCNTL_H_INCLUDED
#endif

#ifndef MODE_T
#  ifdef _WIN32
#    define MODE_T int
#  else
#    define MODE_T mode_t
#  endif
#endif

int __VERIFIER_nondet_int(void);

int __CPROVER_creat(const char *pathname, MODE_T mode)
{
__CPROVER_HIDE:;
  int return_value = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value >= -1);
  (void)*pathname;
  (void)mode;
  return return_value;
}

/* FUNCTION: creat */

#ifndef __CPROVER_FCNTL_H_INCLUDED
#  include <fcntl.h>
#  define __CPROVER_FCNTL_H_INCLUDED
#endif

#ifndef MODE_T
#  ifdef _WIN32
#    define MODE_T int
#  else
#    define MODE_T mode_t
#  endif
#endif

int __CPROVER_creat(const char *, MODE_T);

int creat(const char *pathname, MODE_T mode)
{
  return __CPROVER_creat(pathname, mode);
}

/* FUNCTION: _creat */

#ifndef __CPROVER_FCNTL_H_INCLUDED
#  include <fcntl.h>
#  define __CPROVER_FCNTL_H_INCLUDED
#endif

#ifndef MODE_T
#  ifdef _WIN32
#    define MODE_T int
#  else
#    define MODE_T mode_t
#  endif
#endif

int __CPROVER_creat(const char *, MODE_T);

int _creat(const char *pathname, MODE_T mode)
{
  return __CPROVER_creat(pathname, mode);
}

/* FUNCTION: creat64 */

#ifndef __CPROVER_FCNTL_H_INCLUDED
#  include <fcntl.h>
#  define __CPROVER_FCNTL_H_INCLUDED
#endif

#ifndef MODE_T
#  ifdef _WIN32
#    define MODE_T int
#  else
#    define MODE_T mode_t
#  endif
#endif

int __CPROVER_creat(const char *, MODE_T);

int creat64(const char *pathname, MODE_T mode)
{
  return __CPROVER_creat(pathname, mode);
}

/* FUNCTION: __CPROVER_openat */

#ifndef __CPROVER_FCNTL_H_INCLUDED
#  include <fcntl.h>
#  define __CPROVER_FCNTL_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int __CPROVER_openat(int dirfd, const char *pathname, int flags)
{
__CPROVER_HIDE:;
  if(dirfd < 0)
  {
    errno = EBADF;
    return -1;
  }

  int return_value = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value >= -1);
  (void)dirfd;
  (void)*pathname;
  (void)flags;
  return return_value;
}

/* FUNCTION: openat */

int __CPROVER_openat(int dirfd, const char *pathname, int flags);

int openat(int dirfd, const char *pathname, int flags, ...)
{
  return __CPROVER_openat(dirfd, pathname, flags);
}

/* FUNCTION: _openat */

int __CPROVER_openat(int dirfd, const char *pathname, int flags);

int _openat(int dirfd, const char *pathname, int flags, ...)
{
  return __CPROVER_openat(dirfd, pathname, flags);
}

/* FUNCTION: openat64 */

int __CPROVER_openat(int dirfd, const char *pathname, int flags);

int openat64(int dirfd, const char *pathname, int flags, ...)
{
  return __CPROVER_openat(dirfd, pathname, flags);
}
