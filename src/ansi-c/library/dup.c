/* FUNCTION: dup */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

int dup(int oldfd)
{
  __CPROVER_HIDE:;
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
  
  return retval;
}

/* FUNCTION: dup2 */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

int dup2(int oldfd, int newfd)
{
  __CPROVER_HIDE:;
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
  
  return retval;
}

/* FUNCTION: dup3 */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int dup3(int oldfd, int newfd, int flags)
{
  __CPROVER_HIDE:;
  (void)oldfd; // Mark as used
  (void)newfd; // Mark as used
  (void)flags; // Mark as used
  
  int retval = __VERIFIER_nondet_int();
  __CPROVER_assume(retval >= -1);
  
  if(retval == -1)
  {
    errno = __VERIFIER_nondet_int();
  }
  
  return retval;
}