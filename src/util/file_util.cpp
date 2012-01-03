/*******************************************************************\

Module: File Utilities

Author: 

Date: January 2012

\*******************************************************************/

#ifdef __linux__
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#endif

#ifdef __FreeBSD_kernel__
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#endif

#ifdef __MACH__
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#endif

#ifdef __CYGWIN__
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#endif

#ifdef _WIN32
#include <io.h>
#include <windows.h>
#include <direct.h>
#include <errno.h>
#define chdir _chdir
#define popen _popen
#define pclose _pclose
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

  char *buf=(char*)malloc(sizeof(char)*bsize);
  if(!buf) abort();
  
  errno=0;
  
  while(buf && getcwd(buf, bsize-1)==NULL && errno==ERANGE)
  {
    bsize*=2;
    buf=(char*)realloc(buf, sizeof(char)*bsize);
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
      remove((path + "/" + ent->d_name).c_str());

    closedir(dir);
  }

  #endif

  rmdir(path.c_str());
}

