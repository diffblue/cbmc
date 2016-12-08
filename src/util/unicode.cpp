/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstring>
#include <locale>
#include <codecvt>

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

  size_t slength=wcslen(s);
  int rlength=WideCharToMultiByte(CP_UTF8, 0, s, slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, s, (int)slength, &r[0], rlength, NULL, NULL);
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

  size_t slength=strlen(s);
  int rlength=MultiByteToWideChar(CP_UTF8, 0, s, (int)slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, s, (int)slength, &r[0], rlength);
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

  size_t slength=s.size();
  int rlength=WideCharToMultiByte(CP_UTF8, 0, &s[0], (int)slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, &s[0], (int)slength, &r[0], rlength, NULL, NULL);
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

  size_t slength=s.size();
  int rlength=MultiByteToWideChar(CP_UTF8, 0, &s[0], (int)slength, NULL, 0);
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
    result+=char(c);
  else if(c<=0x7ff)
  {
    result+=char((c >> 6)   | 0xc0);
    result+=char((c & 0x3f) | 0x80);
  }
  else if(c<=0xffff)
  {
    result+=char((c >> 12)         | 0xe0);
    result+=char(((c >> 6) & 0x3f) | 0x80);
    result+=char((c & 0x3f)        | 0x80);
  }
  else
  {
    result+=char((c >> 18)         | 0xf0);
    result+=char(((c >> 12) & 0x3f)| 0x80);
    result+=char(((c >> 6) & 0x3f) | 0x80);
    result+=char((c & 0x3f)        | 0x80);
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

  for(const auto it : s)
    utf32_to_utf8(it, result);

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

  for(const auto it : s)
    utf32_to_utf8(it, result);

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
  if(argv_wide==NULL) return NULL;

  // the following never gets deleted
  const char **argv_narrow=new const char *[argc+1];
  argv_narrow[argc]=0;

  for(int i=0; i<argc; i++)
    argv_narrow[i]=strdup(narrow(argv_wide[i]).c_str());

  return argv_narrow;
}

std::wstring utf8_to_utf16be(const std::string& in)
{
  std::wstring_convert<std::codecvt_utf8_utf16<wchar_t> > converter;
  return converter.from_bytes(in);
}

std::wstring utf8_to_utf16le(const std::string& in)
{
  std::wstring_convert<std::codecvt_utf8_utf16<wchar_t,0x10ffffUL,std::codecvt_mode::little_endian> > converter;
  return converter.from_bytes(in);
}

std::string utf16le_to_ascii(const std::wstring& in)
{
  std::string result;
  std::locale loc;
  for(const auto c : in)
  {
    if(c <= 255 && isprint(c,loc))
      result+=(unsigned char)c;
    else
    {
      result+="\\u";
      char hex[5];
      sprintf(hex,"%04x",(wchar_t)c);
      result+=hex;
    }
  }
  return result;
}
