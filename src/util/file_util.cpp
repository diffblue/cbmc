/*******************************************************************\

Module: File Utilities

Author:

Date: January 2012

\*******************************************************************/

#include <cerrno>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#include <dirent.h>
#include <cstdlib>
#include <cstdio>
#include <sys/stat.h>
#endif

#ifdef _WIN32
#include <io.h>
#include <windows.h>
#include <direct.h>
#define chdir _chdir
#define popen _popen
#define pclose _pclose
#endif

#ifdef USE_BOOST
#include <boost/filesystem.hpp>
#endif

#include "file_util.h"


/*******************************************************************\

Function: get_current_working_directory

  Inputs: none

 Outputs: current working directory

 Purpose:

\*******************************************************************/

std::string get_current_working_directory()
{
  unsigned bsize=50;

  char *buf=reinterpret_cast<char*>(malloc(sizeof(char)*bsize));
  if(!buf)
    abort();

  errno=0;

  while(buf && getcwd(buf, bsize-1)==NULL && errno==ERANGE)
  {
    bsize*=2;
    buf=reinterpret_cast<char*>(realloc(buf, sizeof(char)*bsize));
  }

  std::string working_directory=buf;
  free(buf);

  return working_directory;
}

/*******************************************************************\

Function: delete_directory

  Inputs: path

 Outputs:

 Purpose: deletes all files in 'path' and then the directory itself

\*******************************************************************/

void delete_directory(const std::string &path)
{
  #ifdef _WIN32

  std::string pattern=path+"\\*";

  // NOLINTNEXTLINE(readability/identifiers)
  struct _finddata_t info;

  intptr_t handle=_findfirst(pattern.c_str(), &info);

  if(handle!=-1)
  {
    unlink(info.name);

    while(_findnext(handle, &info)!=-1)
      unlink(info.name);
  }

  #else

  DIR *dir=opendir(path.c_str());

  if(dir!=NULL)
  {
    struct dirent *ent;

    while((ent=readdir(dir))!=NULL)
      remove((path+"/"+ent->d_name).c_str());

    closedir(dir);
  }

  #endif

  rmdir(path.c_str());
}

/*******************************************************************\

Function: concat_dir_file

  Inputs: directory name and file name

 Outputs: concatenation of directory and file, if the file path is
          relative

 Purpose:

\*******************************************************************/

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





#include <fstream>
#include <cstdlib>
#include <algorithm>
#include <sstream>
#include <vector>

#if defined(WIN32)
#   include <windows.h>
#elif defined(__linux__) || defined(__APPLE__)
#   include <sys/stat.h>
#endif


static std::string::size_type  fileutl_parse_last_dir_pos(
    std::string const&  file_pathname
    )
{
  std::string::size_type const  last_slash_pos =
      file_pathname.find_last_of('/');
  std::string::size_type const  last_backslash_pos =
      file_pathname.find_last_of('\\');
  std::string::size_type const  last_dir_pos =
          last_slash_pos == std::string::npos ?
                 (last_backslash_pos == std::string::npos ?
                    0ULL :
                    last_backslash_pos + 1ULL) :
                 (last_backslash_pos == std::string::npos ?
                    last_slash_pos + 1ULL :
                    (last_slash_pos < last_backslash_pos ?
                       last_backslash_pos :
                       last_slash_pos))
                 ;
  return last_dir_pos;
}


bool  fileutl_file_exists(std::string const&  pathname)
{
  std::ifstream  f{pathname,std::ios::binary};
  return f.good();
}

bool  fileutl_is_directory(std::string const&  pathname)
{
  if (!fileutl_file_exists(pathname))
      return false;
# if defined(WIN32)
    return PathIsDirectory(pathname.c_str());
# elif defined(__linux__) || defined(__APPLE__)
  struct stat buf;
  stat(pathname.c_str(), &buf);
  return S_ISDIR(buf.st_mode);
  //return S_ISREG(buf.st_mode); // is file ?
# else
#   error "Unsuported platform."
# endif
}

uint64_t  fileutl_file_size(std::string const&  file_pathname)
{
  std::ifstream  f{file_pathname,std::ios::binary};
  std::streampos const  begin  = f.tellg();
  f.seekg(0ULL,std::ios::end);
  std::streampos const  end = f.tellg();
  return end - begin;
}

std::string  fileutl_parse_name_in_pathname(std::string const&  file_pathname)
{
  return file_pathname.substr(fileutl_parse_last_dir_pos(file_pathname));
}

std::string  fileutl_parse_path_in_pathname(std::string const&  file_pathname)
{
    return file_pathname.substr(0U,fileutl_parse_last_dir_pos(file_pathname));
}

std::string  fileutl_remove_extension(std::string const&  filename)
{
    return filename.substr(0U,filename.find_last_of('.'));
}

void  fileutl_create_directory(std::string const&  pathname)
{
# if defined(WIN32)
    std::system((std::string("mkdir \"") + pathname + "\"").c_str());
# elif defined(__linux__) || defined(__APPLE__)
#ifdef USE_BOOST
  boost::filesystem::create_directories(pathname);
#else
  auto ignore = std::system(
        (std::string("mkdir -p \"") + pathname + "\"").c_str()
        );
  (void)ignore;
#endif
# else
#   error "Unsuported platform."
# endif
}

std::string  fileutl_concatenate_file_paths(std::string const&  left_path,
                                            std::string const&  right_path)
{
  if (left_path.empty())
    return right_path;
  if (right_path.empty())
    return left_path;
  return left_path + "/" + right_path;
}

std::string  fileutl_absolute_path(std::string const&  path)
{
  // TODO: portability - this implementation won't probably work on Windows...
  std::vector<char> buffer(10000,0);
  return realpath(path.c_str(),&buffer.at(0));
}

std::string  fileutl_normalise_path(std::string const&  path)
{
  std::string  result = path;
  std::replace(result.begin(),result.end(),'\\','/');
  std::string::size_type  pos = 0;
  while((pos = result.find("/./",0)) != std::string::npos)
    result.replace(pos,3,"/");
  // TODO: more fixes should be applied (e.g. /../, //, etc.)
  return result;
}

void  fileutl_split_pathname(std::string const&  pathname,
                             std::vector<std::string>& output)
{
  std::istringstream  istr(fileutl_normalise_path(pathname));
  std::string  token;
  while (std::getline(istr,token,'/'))
    output.push_back(token);
}

std::string  fileutl_join_path_parts(std::vector<std::string> const&  parts)
{
  if (parts.empty())
    return "";
  std::string  result = parts.at(0);
  for (uint64_t  i = 1ULL; i < parts.size(); ++i)
  {
    result.push_back('/');
    result.append(parts.at(i));
  }
  return result;
}

std::string  fileutl_get_common_preffix(std::string const&  pathname1,
                                        std::string const&  pathname2)
{
  std::vector<std::string>  split1;
  fileutl_split_pathname(pathname1,split1);

  std::vector<std::string>  split2;
  fileutl_split_pathname(pathname2,split2);

  std::vector<std::string>  common_split;
  for (uint64_t  i = 0ULL, size = std::min(split1.size(),split2.size());
       i < size && split1.at(i) == split2.at(i);
       ++i)
    common_split.push_back(split1.at(i));

  std::string const  result = fileutl_join_path_parts(common_split);
  return result;
}

std::string  fileutl_get_relative_path(std::string const&  pathname,
                                       std::string const&  directory)
{
  std::vector<std::string>  split1;
  fileutl_split_pathname(pathname,split1);
  std::reverse(split1.begin(),split1.end());

  std::vector<std::string>  split2;
  fileutl_split_pathname(directory,split2);
  std::reverse(split2.begin(),split2.end());

  while (!split1.empty() && !split2.empty() && split1.back() == split2.back())
  {
    split1.pop_back();
    split2.pop_back();
  }

  std::reverse(split1.begin(),split1.end());
  std::string const  result = fileutl_join_path_parts(split1);
  return result;
}
