/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#include "tempdir.h"

#ifdef _WIN32
#include <util/pragma_push.def>
#ifdef _MSC_VER
#pragma warning(disable:4668)
  // using #if/#elif on undefined macro
#endif
#include <windows.h>
#include <io.h>
#include <direct.h>
#include <util/pragma_pop.def>
#endif

#include <cstdlib>
#include <vector>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#include "invariant.h"
#include "file_util.h"

std::string get_temporary_directory(const std::string &name_template)
{
  std::string result;

  #ifdef _WIN32
    DWORD dwBufSize = MAX_PATH+1;
    char lpPathBuffer[MAX_PATH+1];
    DWORD dwRetVal = GetTempPathA(dwBufSize, lpPathBuffer);

    if(dwRetVal > dwBufSize || (dwRetVal == 0))
      throw "GetTempPath failed"; // NOLINT(readability/throw)

    // GetTempFileNameA produces <path>\<pre><uuuu>.TMP
    // where <pre> = "TLO"
    // Thus, we must make the buffer 1+3+4+1+3=12 characters longer.

    char t[MAX_PATH];
    UINT uRetVal=GetTempFileNameA(lpPathBuffer, "TLO", 0, t);
    if(uRetVal == 0)
      throw "GetTempFileName failed"; // NOLINT(readability/throw)

    unlink(t);
    if(_mkdir(t)!=0)
      throw "_mkdir failed";

    result=std::string(t);

  #else
    std::string prefixed_name_template="/tmp/";
    const char *TMPDIR_env=getenv("TMPDIR");
    if(TMPDIR_env!=nullptr)
      prefixed_name_template=TMPDIR_env;
    if(*prefixed_name_template.rbegin()!='/')
      prefixed_name_template+='/';
    prefixed_name_template+=name_template;

    std::vector<char> t(prefixed_name_template.begin(), prefixed_name_template.end());
    t.push_back('\0'); // add the zero
    const char *td = mkdtemp(t.data());
    if(!td)
      throw "mkdtemp failed";
    result=std::string(td);
  #endif

  return result;
}

temp_dirt::temp_dirt(const std::string &name_template)
{
  path=get_temporary_directory(name_template);
}

std::string temp_dirt::operator()(const std::string &file)
{
  return concat_dir_file(path, file);
}

void temp_dirt::clear()
{
  delete_directory(path);
}

temp_dirt::~temp_dirt()
{
  clear();
}
