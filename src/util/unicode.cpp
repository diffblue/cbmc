/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstring>

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

  int slength=static_cast<int>(wcslen(s));
  int rlength=
    WideCharToMultiByte(CP_UTF8, 0, s, slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, s, slength, &r[0], rlength, NULL, NULL);
  return r;

  #else
  // dummy conversion
  std::string r;
  r.reserve(wcslen(s));
  while(*s!=0)
  {
    r+=static_cast<char>(*s);
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

  int slength=static_cast<int>(strlen(s));
  int rlength=
    MultiByteToWideChar(CP_UTF8, 0, s, slength, NULL, 0);
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

  int slength=static_cast<int>(s.size());
  int rlength=
    WideCharToMultiByte(CP_UTF8, 0, &s[0], slength, NULL, 0, NULL, NULL);
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

  int slength=static_cast<int>(s.size());
  int rlength=
    MultiByteToWideChar(CP_UTF8, 0, &s[0], slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, &s[0], slength, &r[0], rlength);
  return r;

  #else
  // dummy conversion
  return std::wstring(s.begin(), s.end());
  #endif
}

/*******************************************************************\

Function: utf32_to_utf8

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void utf32_to_utf8(unsigned int c, std::string &result)
{
  if(c<=0x7f)
    result+=static_cast<char>(c);
  else if(c<=0x7ff)
  {
    result+=static_cast<char>((c >> 6)   | 0xc0);
    result+=static_cast<char>((c & 0x3f) | 0x80);
  }
  else if(c<=0xffff)
  {
    result+=static_cast<char>((c >> 12)         | 0xe0);
    result+=static_cast<char>(((c >> 6) & 0x3f) | 0x80);
    result+=static_cast<char>((c & 0x3f)        | 0x80);
  }
  else
  {
    result+=static_cast<char>((c >> 18)         | 0xf0);
    result+=static_cast<char>(((c >> 12) & 0x3f)| 0x80);
    result+=static_cast<char>(((c >> 6) & 0x3f) | 0x80);
    result+=static_cast<char>((c & 0x3f)        | 0x80);
  }
}

/*******************************************************************\

Function: utf32_to_utf8

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string utf32_to_utf8(const std::basic_string<unsigned int> &s)
{
  std::string result;

  result.reserve(s.size()); // at least that long

  for(const auto c : s)
    utf32_to_utf8(c, result);

  return result;
}

/*******************************************************************\

Function: utf16_to_utf8

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string utf16_to_utf8(const std::basic_string<unsigned short int> &s)
{
  std::string result;

  result.reserve(s.size()); // at least that long

  for(const auto c : s)
    utf32_to_utf8(c, result);

  return result;
}

/*******************************************************************\

Function: narrow_argv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char **narrow_argv(int argc, const wchar_t **argv_wide)
{
  if(argv_wide==NULL)
    return NULL;

  // the following never gets deleted
  const char **argv_narrow=new const char *[argc+1];
  argv_narrow[argc]=0;

  for(int i=0; i<argc; i++)
    argv_narrow[i]=strdup(narrow(argv_wide[i]).c_str());

  return argv_narrow;
}
