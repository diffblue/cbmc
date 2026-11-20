/* FUNCTION: getpwnam */

#ifndef _WIN32

#  ifndef __CPROVER_PWD_H_INCLUDED
#    include <pwd.h>
#    define __CPROVER_PWD_H_INCLUDED
#  endif

unsigned __VERIFIER_nondet_unsigned(void);
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

struct passwd __CPROVER_passwd;

struct passwd *getpwnam(const char *name)
{
  // POSIX.1-2017 getpwnam: "A null pointer shall be returned if the
  // requested entry is not found, or an error occurs."
  (void)*name;

  __CPROVER_bool error = __VERIFIER_nondet___CPROVER_bool();
  if(error)
    return (struct passwd *)0;

  __CPROVER_passwd.pw_name = (char *)name;
  __CPROVER_passwd.pw_uid = __VERIFIER_nondet_unsigned();
  __CPROVER_passwd.pw_gid = __VERIFIER_nondet_unsigned();
  // the strings are non-NULL for a found entry
  static char pw_dir_buf[1];
  __CPROVER_passwd.pw_dir = pw_dir_buf;
  static char pw_shell_buf[1];
  __CPROVER_passwd.pw_shell = pw_shell_buf;
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
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

#  ifndef LIBRARY_CHECK
struct passwd __CPROVER_passwd;
#  endif

struct passwd *getpwuid(uid_t uid)
{
  // POSIX.1-2017 getpwuid: "A null pointer shall be returned if the
  // requested entry is not found, or an error occurs."
  __CPROVER_bool error = __VERIFIER_nondet___CPROVER_bool();
  if(error)
    return (struct passwd *)0;

  static char pw_name_buf[1];
  __CPROVER_passwd.pw_name = pw_name_buf;
  __CPROVER_passwd.pw_uid = uid;
  __CPROVER_passwd.pw_gid = __VERIFIER_nondet_unsigned();
  // the strings are non-NULL for a found entry
  static char pw_dir_buf[1];
  __CPROVER_passwd.pw_dir = pw_dir_buf;
  static char pw_shell_buf[1];
  __CPROVER_passwd.pw_shell = pw_shell_buf;
  return &__CPROVER_passwd;
}

#endif
