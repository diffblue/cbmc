/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#ifdef _WIN32
#include <windows.h>
#include <io.h>
#include <direct.h>
#endif

#include <stdlib.h>
#include <string.h>

#ifdef __MACH__
#include <unistd.h>
#endif

#ifdef __linux__
#include <unistd.h>
#endif

#include "tempdir.h"

/*******************************************************************\

Function: get_temporary_directory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_temporary_directory(const std::string &name_template)
{
  std::string result;

  #ifdef _WIN32    
    DWORD dwBufSize = MAX_PATH;
    char lpPathBuffer[MAX_PATH];
    DWORD dwRetVal = GetTempPath(dwBufSize, lpPathBuffer);

    if(dwRetVal > dwBufSize || (dwRetVal == 0))
      throw "GetTempPath failed";
      
    char t[MAX_PATH];
    
    strncpy(t, name_template.c_str(), MAX_PATH);

    UINT uRetVal=GetTempFileName(lpPathBuffer, "TLO", 0, t);
    if(uRetVal == 0)
      throw "GetTempFileName failed";

    unlink(t);
    if(_mkdir(t)!=0)
      throw "_mkdir failed";

    result=t;

  #else
    char t[1000];
    strncpy(t, name_template.c_str(), 1000);
    const char *td = mkdtemp(t);
    if(!td) throw "mkdtemp failed";
    result=td;
  #endif
    
  return result;
}
