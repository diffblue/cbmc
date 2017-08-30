/*******************************************************************\

Module: File Utilities

Author:

Date: January 2012

\*******************************************************************/

/// \file
/// File Utilities

#include "file_util.h"

#include <cerrno>
#include <cassert>

#include <fstream>
#include <cstring>
#include <cstdlib>
#include <algorithm>
#include <sstream>
#include <vector>

#if defined(__linux__) ||                       \
  defined(__FreeBSD_kernel__) ||                \
  defined(__GNU__) ||                           \
  defined(__unix__) ||                          \
  defined(__CYGWIN__) ||                        \
  defined(__MACH__)
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
  return (file_name.size()>1 &&
          file_name[0]!='/' &&
          file_name[1]!=':') ?
    file_name : directory+"\\"+file_name;
#else
  return (!file_name.empty() && file_name[0]=='/') ?
    file_name : directory+"/"+file_name;
#endif
}

static std::string::size_type fileutl_parse_last_dir_pos(
  std::string const &file_pathname)
{
  auto found = file_pathname.find_last_of("/\\");
  if(found == std::string::npos)
    return 0;
  else
    return found + 1;
}

bool fileutl_file_exists(std::string const &pathname)
{
  std::ifstream f{pathname, std::ios::binary};
  return f.good();
}

bool fileutl_is_directory(std::string const &pathname)
{
  if(!fileutl_file_exists(pathname))
    return false;
# if defined(WIN32)
  return PathIsDirectory(pathname.c_str());
# elif defined(__linux__) || defined(__APPLE__)
  struct stat buf;
  stat(pathname.c_str(), &buf);
  return S_ISDIR(buf.st_mode);
# else
#   error "Unsuported platform."
# endif
}

uint64_t fileutl_file_size(std::string const &file_pathname)
{
  std::ifstream f{file_pathname, std::ios::binary};
  std::streampos const begin = f.tellg();
  f.seekg(0ULL, std::ios::end);
  std::streampos const end = f.tellg();
  return end - begin;
}

std::string fileutl_parse_name_in_pathname(std::string const &file_pathname)
{
  return file_pathname.substr(fileutl_parse_last_dir_pos(file_pathname));
}

std::string fileutl_parse_path_in_pathname(std::string const &file_pathname)
{
  return file_pathname.substr(0U, fileutl_parse_last_dir_pos(file_pathname));
}

std::string fileutl_remove_extension(std::string const &filename)
{
  return filename.substr(0U, filename.find_last_of('.'));
}

void fileutl_create_directory(std::string const &pathname)
{
# if defined(WIN32)
  char path_sep='\\';
#else
  char path_sep='/';
#endif
  std::size_t search_from=0;
  while(search_from!=std::string::npos)
  {
    // Search from after the previous path separator, incidentally
    // skipping trying to create '/' if an absolute path is given
    search_from=pathname.find(path_sep, search_from+1);
    std::string truncated_pathname=pathname.substr(0, search_from);
#if defined(WIN32)
    _mkdir(truncated_pathname.c_str());
#else
    mkdir(truncated_pathname.c_str(), 0777);
#endif
    // Ignore return-- regardless of why we can't create a
    // path prefix, we might as well keep trying down to more
    // specific paths.
  }
}

std::string fileutl_concatenate_file_paths(
  std::string const &left_path,
  std::string const &right_path)
{
  if(left_path.empty())
    return right_path;
  if(right_path.empty())
    return left_path;
  return left_path + "/" + right_path;
}

std::string fileutl_absolute_path(std::string const &path)
{
#if defined(WIN32)
  DWORD buffer_length = GetFullPathName(path.c_str(), 0, nullptr, nullptr);
  std::vector<char> buffer(buffer_length);
  DWORD actual_length =
    GetFullPathName(path.c_str(), buffer_length, &(buffer[0]), nullptr);
  if(actual_length != buffer_length - 1)
    throw "fileutl_absolute_path: GetFullPathName failed";
  return std::string(&(buffer[0]));
#else
  char *absolute = realpath(path.c_str(), nullptr);
  if(absolute==NULL)
  {
    std::string error=std::strerror(errno);
    throw std::ios::failure("Could not resolve absolute path ("+error+")");
  }
  std::string ret(absolute);
  free(absolute);
  return ret;
#endif
}

std::string fileutl_normalise_path(std::string const &path)
{
  std::string result = path;
  std::replace(result.begin(), result.end(), '\\', '/');
  std::string::size_type pos = 0ULL;
  while((pos = result.find("//", 0)) != std::string::npos)
    result.replace(pos, 2, "/");
  while((pos = result.find("/./", 0)) != std::string::npos)
    result.replace(pos, 3, "/");
  while((pos = result.find("/../", 0)) != std::string::npos)
  {
    assert(pos != 0ULL);
    const std::string::size_type prev_pos = result.rfind("/", pos-1ULL);
    if(prev_pos == std::string::npos)
      break;
    result.replace(prev_pos, pos - prev_pos + 4ULL, "/");
  }
  return result;
}

void fileutl_split_pathname(
  std::string const &pathname,
  std::vector<std::string> &output)
{
  std::istringstream istr(fileutl_normalise_path(pathname));
  std::string token;
  while(std::getline(istr, token, '/'))
    output.push_back(token);
}

std::string fileutl_join_path_parts(std::vector<std::string> const &parts)
{
  if(parts.empty())
    return "";
  std::string result = parts.at(0);
  for(uint64_t i = 1ULL; i < parts.size(); ++i)
  {
    result.push_back('/');
    result.append(parts.at(i));
  }
  return result;
}

std::string fileutl_get_common_prefix(
  std::string const &pathname1,
  std::string const &pathname2)
{
  std::vector<std::string>  split1;
  fileutl_split_pathname(pathname1, split1);

  std::vector<std::string>  split2;
  fileutl_split_pathname(pathname2, split2);

  std::vector<std::string>  common_split;
  for(uint64_t i = 0ULL, size = std::min(split1.size(), split2.size());
      i < size && split1.at(i) == split2.at(i);
      ++i)
    common_split.push_back(split1.at(i));

  std::string const result = fileutl_join_path_parts(common_split);
  return result;
}

std::string fileutl_get_relative_path(
  std::string const &pathname,
  std::string const &directory)
{
  std::vector<std::string>  split1;
  fileutl_split_pathname(pathname, split1);
  std::reverse(split1.begin(), split1.end());

  std::vector<std::string>  split2;
  fileutl_split_pathname(directory, split2);
  std::reverse(split2.begin(), split2.end());

  while(!split1.empty() && !split2.empty() && split1.back() == split2.back())
  {
    split1.pop_back();
    split2.pop_back();
  }

  std::reverse(split1.begin(), split1.end());
  std::string const result = fileutl_join_path_parts(split1);
  return result;
}

/// Replaces invalid characters in a file name using a hard-coded list of
/// replacements.
/// This is not designed to operate on path names and will replace folder
/// seperator characters.
/// \param file_name: The file name to sanitize.
std::string make_valid_filename(std::string file_name)
{
  std::replace(file_name.begin(), file_name.end(), '#', '_');
  std::replace(file_name.begin(), file_name.end(), '$', '_');
  std::replace(file_name.begin(), file_name.end(), ':', '.');
  std::replace(file_name.begin(), file_name.end(), '/', '.');
  std::replace(file_name.begin(), file_name.end(), '\\', '.');
  std::replace(file_name.begin(), file_name.end(), '<', '[');
  std::replace(file_name.begin(), file_name.end(), '>', ']');
  return file_name;
}
