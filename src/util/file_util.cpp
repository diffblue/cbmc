/*******************************************************************\

Module: File Utilities

Author:

Date: January 2012

\*******************************************************************/

/// \file
/// File Utilities

#include "file_util.h"

#include "exception_utils.h"

#include <cerrno>
#include <cstring>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <sys/stat.h>
#include <unistd.h>
#include <dirent.h>
#include <cstdlib>
#include <cstdio>
#endif

#ifdef _WIN32
#include <util/pragma_push.def>
#ifdef _MSC_VER
#pragma warning(disable:4668)
  // using #if/#elif on undefined macro
#endif
#include <io.h>
#include <windows.h>
#include <direct.h>
#include <util/unicode.h>
#define chdir _chdir
#define popen _popen
#define pclose _pclose
#include <util/pragma_pop.def>
#endif

/// \return current working directory
std::string get_current_working_directory()
{
  #ifndef _WIN32
  errno=0;
  char *wd=realpath(".", nullptr);

  if(wd == nullptr || errno != 0)
    throw system_exceptiont(
      std::string("realpath failed: ") + std::strerror(errno));

  std::string working_directory=wd;
  free(wd);
  #else
  char buffer[4096];
  DWORD retval=GetCurrentDirectory(4096, buffer);
  if(retval == 0)
    throw system_exceptiont("failed to get current directory of process");
  std::string working_directory(buffer);
  #endif

  return working_directory;
}

/// deletes all files in 'path' and then the directory itself
#ifdef _WIN32

void delete_directory_utf16(const std::wstring &path)
{
  std::wstring pattern=path + L"\\*";
  // NOLINTNEXTLINE(readability/identifiers)
  struct _wfinddata_t info;
  intptr_t hFile=_wfindfirst(pattern.c_str(), &info);
  if(hFile!=-1)
  {
    do
    {
      if(wcscmp(info.name, L".")==0 || wcscmp(info.name, L"..")==0)
        continue;
      std::wstring sub_path=path+L"\\"+info.name;
      if(info.attrib & _A_SUBDIR)
        delete_directory_utf16(sub_path);
      else
        DeleteFileW(sub_path.c_str());
    }
    while(_wfindnext(hFile, &info)==0);
    _findclose(hFile);
    RemoveDirectoryW(path.c_str());
  }
}

#endif

void delete_directory(const std::string &path)
{
#ifdef _WIN32
  delete_directory_utf16(utf8_to_utf16_native_endian(path));
#else
  DIR *dir=opendir(path.c_str());
  if(dir!=nullptr)
  {
    struct dirent *ent;
    while((ent=readdir(dir))!=nullptr)
    {
      // Needed for Alpine Linux
      if(strcmp(ent->d_name, ".")==0 || strcmp(ent->d_name, "..")==0)
        continue;

      std::string sub_path=path+"/"+ent->d_name;

      struct stat stbuf;
      int result=stat(sub_path.c_str(), &stbuf);
      if(result!=0)
        throw system_exceptiont(
          std::string("Stat failed: ") + std::strerror(errno));

      if(S_ISDIR(stbuf.st_mode))
        delete_directory(sub_path);
      else
      {
        result=remove(sub_path.c_str());
        if(result!=0)
          throw system_exceptiont(
            std::string("Remove failed: ") + std::strerror(errno));
      }
    }
    closedir(dir);
  }
  rmdir(path.c_str());
#endif
}

/// \par parameters: directory name and file name
/// \return concatenation of directory and file, if the file path is relative
std::string concat_dir_file(
  const std::string &directory,
  const std::string &file_name)
{
  #ifdef _WIN32
  return (file_name.size() > 1 && file_name[0] != '/' && file_name[1] == ':') ?
          file_name : directory + "\\" + file_name;
  #else
  return (!file_name.empty() && file_name[0]=='/') ?
          file_name : directory+"/"+file_name;
  #endif
}

bool is_directory(const std::string &path)
{
  if(path.empty())
    return false;

#ifdef _WIN32

  auto attributes = ::GetFileAttributesW(widen(path).c_str());
  if (attributes == INVALID_FILE_ATTRIBUTES)
    return false;
  else
    return (attributes & FILE_ATTRIBUTE_DIRECTORY) != 0;

#else

  struct stat buf;

  if(stat(path.c_str(), &buf)!=0)
    return false;
  else
    return (buf.st_mode & S_IFDIR) != 0;

#endif
}
