/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "unicode.h"

#ifdef _WIN32
#include <windows.h>
#endif

/*******************************************************************\

Function: narrow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define BUFSIZE 100

std::string narrow(const wchar_t *s)
{
  #ifdef _WIN32

  int slength=wcslen(s);
  int rlength=WideCharToMultiByte(CP_UTF8, 0, s, slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, s, slength, &r[0], rlength, NULL, NULL);
  return r;

  #else
  // dummy conversion
  std::string r;
  r.reserve(wcslen(s));
  while(*s!=0)
  {
    r+=char(*s);
    s++;
  }
  
  return r;
  #endif
}

/*******************************************************************\

Function: widen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::wstring widen(const char *s)
{
  #ifdef _WIN32

  int slength=strlen(s);
  int rlength=MultiByteToWideChar(CP_UTF8, 0, s, slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, s, slength, &r[0], rlength);
  return r;

  #else
  // dummy conversion
  std::wstring r;
  r.reserve(strlen(s));
  while(*s!=0)
  {
    r+=wchar_t(*s);
    s++;
  }
  
  return r;
  #endif
}

/*******************************************************************\

Function: narrow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string narrow(const std::wstring &s)
{
  #ifdef _WIN32

  int slength=s.size();
  int rlength=WideCharToMultiByte(CP_UTF8, 0, &s[0], slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, &s[0], slength, &r[0], rlength, NULL, NULL);
  return r;
  
  #else
  // dummy conversion
  return std::string(s.begin(), s.end());
  #endif
}

/*******************************************************************\

Function: widen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::wstring widen(const std::string &s)
{
  #ifdef _WIN32

  int slength=s.size();
  int rlength=MultiByteToWideChar(CP_UTF8, 0, &s[0], slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, &s[0], slength, &r[0], rlength);
  return r;

  #else
  // dummy conversion
  return std::wstring(s.begin(), s.end());
  #endif
}

/*******************************************************************\

Function: narrow_argv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef _WIN32
const char **narrow_argv()
{
  int argc;
  wchar_t **argv_wide=
    CommandLineToArgvW(GetCommandLineW(), &argc);

  // the following never gets deleted
  const char **argv_narrow=new const char *[argc];
    
  for(int i=0; i<argc; i++)
    argv_narrow[i]=strdup(narrow(argv_wide[i]).c_str());
  
  return argv_narrow;
}
#endif
