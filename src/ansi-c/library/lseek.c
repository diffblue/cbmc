/* FUNCTION: lseek */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#  include <sys/types.h>
#  define __CPROVER_SYS_TYPES_H_INCLUDED
#endif

long __VERIFIER_nondet_long(void);
int __VERIFIER_nondet_int(void);

off_t lseek(int fd, off_t offset, int whence)
{
  __CPROVER_HIDE:;
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
  
  return (off_t)retval;
}
