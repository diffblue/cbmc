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

#include "file_util.h"
#include "invariant.h"

std::string get_temporary_directory(const std::string &name_template)
{
  std::string result;

  #ifdef _WIN32
    DWORD dwBufSize = MAX_PATH+1;
    char lpPathBuffer[MAX_PATH+1];
    DWORD dwRetVal = GetTempPathA(dwBufSize, lpPathBuffer);

    // happy to join these two into single statement if preferred
    CHECK_RETURN(dwRetVal <= dwBufSize)
    CHECK_RETURN(dwRetVal != 0);

    // GetTempFileNameA produces <path>\<pre><uuuu>.TMP
    // where <pre> = "TLO"
    // Thus, we must make the buffer 1+3+4+1+3=12 characters longer.

    char t[MAX_PATH];
    UINT uRetVal=GetTempFileNameA(lpPathBuffer, "TLO", 0, t);
    CHECK_RETURN(uRetVal != 0);

    unlink(t);
    int retVal_mkdir{_mkdir(t)};
    // returns 0 for success, -1 for directory creation failure
    CHECK_RETURN(retVal_mkdir==0)

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
    CHECK_RETURN(td!=nullptr);
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
    CHECK_RETURN(false);
}

temp_working_dirt::~temp_working_dirt()
{
  if(chdir(old_working_directory.c_str())!=0)
    CHECK_RETURN(false);
}
