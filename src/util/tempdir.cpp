/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#include "tempdir.h"

#ifdef _WIN32
#include <windows.h>
#include <io.h>
#include <direct.h>
#endif

#include <cassert>
#include <cstdlib>
#include <cstring>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#include "file_util.h"

std::string get_temporary_directory(const std::string &name_template)
{
  std::string result;

  #ifdef _WIN32
    DWORD dwBufSize = MAX_PATH;
    char lpPathBuffer[MAX_PATH];
    DWORD dwRetVal = GetTempPathA(dwBufSize, lpPathBuffer);

    if(dwRetVal > dwBufSize || (dwRetVal == 0))
      throw "GetTempPath failed"; // NOLINT(readability/throw)

    char t[MAX_PATH];

    strncpy(t, name_template.c_str(), MAX_PATH);

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
    if(TMPDIR_env!=0)
      prefixed_name_template=TMPDIR_env;
    if(*prefixed_name_template.rbegin()!='/')
      prefixed_name_template+='/';
    prefixed_name_template+=name_template;

    char t[1000];
    strncpy(t, prefixed_name_template.c_str(), 1000);
    const char *td = mkdtemp(t);
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

temp_working_dirt::temp_working_dirt(const std::string &name_template):
  temp_dirt(name_template)
{
  old_working_directory=get_current_working_directory();
  if(chdir(path.c_str())!=0)
    assert(false);
}

temp_working_dirt::~temp_working_dirt()
{
  if(chdir(old_working_directory.c_str())!=0)
    assert(false);
}
