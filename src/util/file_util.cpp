/*******************************************************************\

Module: File Utilities

Author:

Date: January 2012

\*******************************************************************/

/// \file
/// File Utilities

#include "file_util.h"

#include <cerrno>

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
#include <io.h>
#include <windows.h>
#include <direct.h>
#include <util/unicode.h>
#define chdir _chdir
#define popen _popen
#define pclose _pclose
#else
#include <cstring>
#endif

/// \return current working directory
std::string get_current_working_directory()
{
  unsigned bsize=50;

  char *buf=reinterpret_cast<char*>(malloc(sizeof(char)*bsize));
  if(!buf)
    abort();

  errno=0;

  while(buf && getcwd(buf, bsize-1)==nullptr && errno==ERANGE)
  {
    bsize*=2;
    buf=reinterpret_cast<char*>(realloc(buf, sizeof(char)*bsize));
  }

  std::string working_directory=buf;
  free(buf);

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
  delete_directory_utf16(utf8_to_utf16_little_endian(path));
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
        throw std::string("Stat failed: ")+std::strerror(errno);

      if(S_ISDIR(stbuf.st_mode))
        delete_directory(sub_path);
      else
      {
        result=remove(sub_path.c_str());
        if(result!=0)
          throw std::string("Remove failed: ")+std::strerror(errno);
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
  return  (file_name.size()>1 &&
           file_name[0]!='/' &&
           file_name[1]!=':') ?
           file_name : directory+"\\"+file_name;
  #else
  return (!file_name.empty() && file_name[0]=='/') ?
          file_name : directory+"/"+file_name;
  #endif
}
