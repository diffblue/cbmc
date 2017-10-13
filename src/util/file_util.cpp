/*******************************************************************\

Module: File Utilities

Author:

Date: January 2012

\*******************************************************************/

/// \file
/// File Utilities

#include "file_util.h"

#include "invariant.h"

#include <cerrno>
#include <cstring>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <fstream>
#include <cstring>
#include <cstdlib>
#include <algorithm>
#include <sstream>
#include <vector>

#include <unistd.h>
#include <dirent.h>
#include <cstdio>
#include <sys/stat.h>
#endif

#ifdef _WIN32
#include <io.h>
#define NOMINMAX // Don't define 'min', masking std::min
#include <windows.h>
#include <direct.h>
#include <Shlwapi.h>
#undef NOMINMAX
#include <util/unicode.h>
#define chdir _chdir
#define popen _popen
#define pclose _pclose
#endif

/// \return current working directory
std::string get_current_working_directory()
{
  #ifndef _WIN32
  errno=0;
  char *wd=realpath(".", nullptr);
  INVARIANT(
    wd!=nullptr && errno==0,
    std::string("realpath failed: ")+strerror(errno));

  std::string working_directory=wd;
  free(wd);
  #else
  char buffer[4096];
  DWORD retval=GetCurrentDirectory(4096, buffer);
  CHECK_RETURN(retval>0);
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

/// Checks that a path corresponds to an existing file.
/// \param pathname: path to check
/// \return true if existing directory
bool fileutil_is_file(const std::string &pathname)
{
# if defined(WIN32)
  return PathFileExists(pathname.c_str()) && !PathIsDirectory(pathname.c_str());
# elif defined(__linux__) || defined(__APPLE__)
  struct stat buf;
  int ret=stat(pathname.c_str(), &buf);
  return !ret && S_ISREG(buf.st_mode);
# else
#   error "Unsuported platform."
# endif
}

/// Checks that a path corresponds to an existing directory.
/// \param pathname: path to check
/// \return true if existing directory
bool fileutil_is_directory(const std::string &pathname)
{
# if defined(WIN32)
  return PathIsDirectory(pathname.c_str());
# elif defined(__linux__) || defined(__APPLE__)
  struct stat buf;
  int ret=stat(pathname.c_str(), &buf);
  return !ret && S_ISDIR(buf.st_mode);
# else
#   error "Unsuported platform."
# endif
}

/// Gets the size of an existing file.
/// \param filename: file to query
/// \return size in bytes
/// \throws fileutil_error on error
uint64_t fileutil_file_size(const std::string &filename)
{
  std::ifstream f{filename, std::ios::binary};
  if(!f.good())
    throw fileutil_error("Couldn't open "+filename+" for reading");
  const std::streampos begin=f.tellg();
  if(begin==-1)
    throw fileutil_error("Couldn't read start position of "+filename);
  f.seekg(0ULL, std::ios::end);
  if(!f.good())
    throw fileutil_error("Couldn't seek to end of "+filename);
  const std::streampos end=f.tellg();
  if(end==-1)
    throw fileutil_error("Couldn't read end position of "+filename);
  return end-begin;
}

/// Finds last path element offset
/// \param path: path to find path separators in
/// \return offset of the start of the last element in path, or zero if empty.
static std::string::size_type last_path_element(const std::string &path)
{
  auto found=path.rfind(PATH_SEPARATOR, path.size()-1);
  return found==std::string::npos ? 0 : found+1;
}

/// Path to filename.
/// \param path: path to extract filename from
/// \return part of path after the last path separator, or all of path if none
std::string fileutil_path_filename(const std::string &path)
{
  return path.substr(last_path_element(path));
}

/// Path to directory name.
/// \param path: path to extract directory name from
/// \return part of path after the last path separator, or all of path if none
std::string fileutil_path_dirname(const std::string &path)
{
  return path.substr(0, last_path_element(path));
}

/// Removes file extension from a path
/// \param path: path to remove extension from
/// \return path with file extension removed, or path if non found
std::string fileutil_remove_extension(const std::string &path)
{
  // Conveniently, rfind returns npos on failure, which also
  // corresponds to removing nothing from path.
  return path.substr(0, path.rfind('.'));
}

/// Creates a single directory
/// \param path: directory to create
/// \throws fileutil_error if creation fails, including because already exists
void fileutil_create_directory(const std::string &path)
{
  int ret=
#if defined(WIN32)
    _mkdir(path.c_str());
#else
    mkdir(path.c_str(), 0777);
#endif

  if(ret==-1)
  {
    throw fileutil_error(
      "Failed to create directory "+path+": "+strerror(errno));
  }
}

/// Recursively creates directories
/// \param path: directories to create
/// \throws fileutil_error on first failure
void fileutil_create_directories(const std::string &path)
{
  std::size_t search_from=0;
  do
  {
    // Search from after the previous path separator, incidentally
    // skipping trying to create '/' if an absolute path is given
    search_from=path.find(PATH_SEPARATOR, search_from+1);
    std::string truncated_path=path.substr(0, search_from);
    if(!fileutil_is_directory(truncated_path))
      fileutil_create_directory(truncated_path);
  } while(search_from!=std::string::npos);
}

/// Get absolute, canonical version of path
/// \param path: perhaps-relative path
/// \return absolute path
/// \throws fileutil_error on failure
std::string fileutil_absolute_path(const std::string &path)
{
#if defined(WIN32)
  DWORD buffer_length=GetFullPathName(path.c_str(), 0, nullptr, nullptr);
  std::vector<char> buffer(buffer_length);
  DWORD actual_length=
    GetFullPathName(path.c_str(), buffer_length, &(buffer[0]), nullptr);
  if(actual_length!=buffer_length-1)
    throw fileutil_error("fileutil_absolute_path: GetFullPathName failed");
  return std::string(&(buffer[0]));
#else
  std::vector<char> buf(PATH_MAX);
  char *absolute=realpath(path.c_str(), buf.data());
  if(absolute==nullptr)
  {
    throw fileutil_error(
      std::string("Failed resolving absolute path: ")+strerror(errno));
  }
  return std::string(absolute);
#endif
}

/// Splits a path into path-separator-delimited elements
/// \param path: path to split
/// \return vector of path elements
std::vector<std::string> fileutil_split_path(
  const std::string &path)
{
  std::vector<std::string> output;
  std::istringstream istr(path);
  std::string token;
  while(std::getline(istr, token, PATH_SEPARATOR))
    output.push_back(token);
  return output;
}

/// Joins a vector of path elements with path separators added as needed
/// \param parts: vector of elements
/// \return joined path
std::string fileutil_join_path(const std::vector<std::string> &parts)
{
  std::ostringstream ostr;
  bool empty=true, ends_with_separator=false;
  for(const std::string &part : parts)
  {
    if(part.empty())
      throw fileutil_error("Empty path element passed to fileutil_join_path");
    if(!(empty || ends_with_separator))
      ostr << PATH_SEPARATOR;
    ostr << part;
    empty=false;
    ends_with_separator=(part.back()==PATH_SEPARATOR);
  }
  return ostr.str();
}

/// Get a common prefix for path1 and path2 (e.g. `/x/y/z` and `/x/yw` have
/// common prefix `/x`). Note paths are not canonicalised first.
/// \param path1: first path
/// \param path2: second path
/// \return common prefix
std::string fileutil_get_common_prefix(
  const std::string &path1,
  const std::string &path2)
{
  const std::string &shorter_path=path1.size()<path2.size() ? path1 : path2;
  const std::string &longer_path=&shorter_path==&path1 ? path2 : path1;

  auto mismatch_iterators=std::mismatch(
    shorter_path.begin(), shorter_path.end(), longer_path.begin());

  // No match?
  if(mismatch_iterators.first==shorter_path.begin())
    return "";

  // Full match?
  if(mismatch_iterators.second==longer_path.end())
    return path1;

  // Full match of shorter_path?
  if(mismatch_iterators.first==shorter_path.end() &&
     *mismatch_iterators.second==PATH_SEPARATOR)
    return shorter_path;

  // Mismatch in shorter_path. Strip last path component:
  std::string matching_part=
    shorter_path.substr(
      0, std::distance(shorter_path.begin(), mismatch_iterators.first));

  return fileutil_path_dirname(matching_part);
}

/// Expresses a path relative to a directory if it is a prefix, or returns it
/// unchanged otherwise. Note neither is canonicalised first.
/// \param path: path to strip of prefix
/// \param directory: directory prefix to remove if found
/// \return relative path if applicable or passed path otherwise.
std::string fileutil_get_relative_path(
  const std::string &path,
  const std::string &directory)
{
  // Remove prefix if directory is a prefix of path and the prefix
  // aligns to a path element boundary:
  if(directory.size()<path.size() &&
     !path.compare(0, directory.size(), path) &&
     (path[directory.size()-1]==PATH_SEPARATOR ||
      path[directory.size()]==PATH_SEPARATOR))
  {
    // Remove prefix separator if present:
    std::string ret=path.substr(directory.size());
    if(ret[0]==PATH_SEPARATOR)
      ret=ret.substr(1);
    return ret;
  }

  // Failed, keep existing path
  return path;
}

/// Replaces invalid characters in a file name using a hard-coded list of
/// replacements.
/// This is not designed to operate on path names and will replace folder
/// seperator characters.
/// \param file_name: The file name to sanitize.
/// \return file_name with characters #$:/\<> replaced by .....[] respectively
std::string fileutil_make_valid_filename(std::string file_name)
{
  std::replace(file_name.begin(), file_name.end(), '#', '.');
  std::replace(file_name.begin(), file_name.end(), '$', '.');
  std::replace(file_name.begin(), file_name.end(), ':', '.');
  std::replace(file_name.begin(), file_name.end(), '/', '.');
  std::replace(file_name.begin(), file_name.end(), '\\', '.');
  std::replace(file_name.begin(), file_name.end(), '<', '[');
  std::replace(file_name.begin(), file_name.end(), '>', ']');
  return file_name;
}
