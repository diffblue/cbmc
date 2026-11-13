/* FUNCTION: getpid */

int __VERIFIER_nondet_int(void);

int getpid(void)
{
  __CPROVER_HIDE:;
  // getpid() returns the process ID
  // Process IDs are positive integers
  int pid = __VERIFIER_nondet_int();
  __CPROVER_assume(pid > 0);
  return pid;
}

/* FUNCTION: getuid */

#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#  include <sys/types.h>
#  define __CPROVER_SYS_TYPES_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

uid_t getuid(void)
{
  __CPROVER_HIDE:;
  // getuid() returns the user ID
  // UIDs are non-negative
  int uid = __VERIFIER_nondet_int();
  __CPROVER_assume(uid >= 0);
  return (uid_t)uid;
}

/* FUNCTION: getgid */

#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#  include <sys/types.h>
#  define __CPROVER_SYS_TYPES_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

gid_t getgid(void)
{
  __CPROVER_HIDE:;
  // getgid() returns the group ID
  int gid = __VERIFIER_nondet_int();
  __CPROVER_assume(gid >= 0);
  return (gid_t)gid;
}

/* FUNCTION: geteuid */

#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#  include <sys/types.h>
#  define __CPROVER_SYS_TYPES_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

uid_t geteuid(void)
{
  __CPROVER_HIDE:;
  // geteuid() returns the effective user ID
  int euid = __VERIFIER_nondet_int();
  __CPROVER_assume(euid >= 0);
  return (uid_t)euid;
}

/* FUNCTION: getegid */

#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#  include <sys/types.h>
#  define __CPROVER_SYS_TYPES_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

gid_t getegid(void)
{
  __CPROVER_HIDE:;
  // getegid() returns the effective group ID
  int egid = __VERIFIER_nondet_int();
  __CPROVER_assume(egid >= 0);
  return (gid_t)egid;
}

/* FUNCTION: gettid */

#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#  include <sys/types.h>
#  define __CPROVER_SYS_TYPES_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

pid_t gettid(void)
{
  __CPROVER_HIDE:;
  // gettid() returns the thread ID
  int tid = __VERIFIER_nondet_int();
  __CPROVER_assume(tid > 0);
  return (pid_t)tid;
}
