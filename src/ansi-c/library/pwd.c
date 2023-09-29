/* FUNCTION: getpwnam */

#ifndef _WIN32

#  ifndef __CPROVER_PWD_H_INCLUDED
#    include <pwd.h>
#    define __CPROVER_PWD_H_INCLUDED
#  endif

unsigned __VERIFIER_nondet_unsigned(void);

struct passwd __CPROVER_passwd;

struct passwd *getpwnam(const char *name)
{
  // make some fields non-null
  __CPROVER_passwd.pw_name = (char *)name;
  __CPROVER_passwd.pw_uid = __VERIFIER_nondet_unsigned();
  __CPROVER_passwd.pw_gid = __VERIFIER_nondet_unsigned();
  return &__CPROVER_passwd;
}

#endif

/* FUNCTION: getpwuid */

#ifndef _WIN32

#  ifndef __CPROVER_PWD_H_INCLUDED
#    include <pwd.h>
#    define __CPROVER_PWD_H_INCLUDED
#  endif

unsigned __VERIFIER_nondet_unsigned(void);

#  ifndef LIBRARY_CHECK
struct passwd __CPROVER_passwd;
#  endif

struct passwd *getpwuid(uid_t uid)
{
  // make some fields non-null
  __CPROVER_passwd.pw_uid = uid;
  __CPROVER_passwd.pw_gid = __VERIFIER_nondet_unsigned();
  return &__CPROVER_passwd;
}

#endif
