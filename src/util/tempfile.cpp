/*******************************************************************\

Module:

Author: Daniel Kroening

\*******************************************************************/

#include "tempfile.h"

#ifdef _WIN32
#include <util/pragma_push.def>
#ifdef _MSC_VER
#pragma warning(disable:4668)
  // using #if/#elif on undefined macro
#endif
#include <process.h>
#include <sys/stat.h>
#include <windows.h>
#include <io.h>
#include <tchar.h>
#define getpid _getpid
#define open _open
#define close _close
#include <util/pragma_pop.def>
#endif

#include <fcntl.h>

#include <cstdlib>
#include <cstdio>
#include <cstring>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

/// Substitute for mkstemps (OpenBSD standard) for Windows, where it is
/// unavailable.
#ifdef _WIN32
#define mkstemps my_mkstemps
int my_mkstemps(char *template_str, int suffix_len)
{
  // The template should be of the form tmpXXXXXXsuffix

  std::size_t template_length=strlen(template_str);

  if(suffix_len<0)
    return -1;

  if(static_cast<std::size_t>(suffix_len+6)>template_length)
    return -1; // suffix too long

  char *XXXXXX_pos=
    template_str+template_length-6-suffix_len;

  if(strncmp(XXXXXX_pos, "XXXXXX", 6)!=0)
    return -1; // XXXXXX missing

  static const char letters_and_numbers[]=
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";

  static long long unsigned int random_state;
  random_state+=getpid()+123;

  for(unsigned attempt = 0; attempt < 1000; ++attempt)
  {
    unsigned long long number=random_state;

    for(unsigned i=0; i<6; i++)
    {
      XXXXXX_pos[i]=letters_and_numbers[number%62];
      number/=62;
    }

    int fd=open(template_str, O_RDWR|O_CREAT|O_EXCL, 0600);
    if(fd>=0)
      return fd; // ok

    random_state+=4321+getpid(); // avoid repeating
  }

  template_str[0]=0;
  return -1; // error
}
#endif

std::string get_temporary_file(
  const std::string &prefix,
  const std::string &suffix)
{
  #ifdef _WIN32
  char lpTempPathBuffer[MAX_PATH];
  DWORD dwRetVal;

  dwRetVal=
    GetTempPathA(
      MAX_PATH,          // length of the buffer
      lpTempPathBuffer); // buffer for path

  if(dwRetVal>MAX_PATH || (dwRetVal==0))
    throw "GetTempPath failed"; // NOLINT(readability/throw)

  // the path returned by GetTempPath ends with a backslash
  std::string t_template=
    std::string(lpTempPathBuffer)+prefix+
    std::to_string(getpid())+".XXXXXX"+suffix;
  #else
  std::string dir="/tmp/";
  const char *TMPDIR_env=getenv("TMPDIR");
  if(TMPDIR_env!=nullptr)
    dir=TMPDIR_env;
  if(*dir.rbegin()!='/')
    dir+='/';

  std::string t_template=
    dir+prefix+std::to_string(getpid())+".XXXXXX"+suffix;
  #endif

  char *t_ptr=strdup(t_template.c_str());

  int fd=mkstemps(t_ptr, suffix.size());

  if(fd<0)
    throw "mkstemps failed";

  close(fd);

  std::string result=std::string(t_ptr);
  free(t_ptr);
  return result;
}

temporary_filet::~temporary_filet()
{
  if(!name.empty())
    std::remove(name.c_str());
}
