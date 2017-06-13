/*******************************************************************\

Module:

Author: CM Wintersteiger

Date:

\*******************************************************************/

#include "get_base_name.h"

/// cleans a filename from path and extension
/// \par parameters: a string
/// \return a new string
std::string get_base_name(const std::string &in, bool strip_suffix)
{
  size_t r=std::string::npos;
  if(strip_suffix)
    r=in.rfind('.', in.length()-1);
  if(r==std::string::npos)
    r=in.length();

  size_t f=in.rfind('/', in.length()-1);
  if(f==std::string::npos)
    f=0;

  size_t fw=in.rfind('\\', in.length()-1);
  if(fw==std::string::npos)
    fw=0;

  f = (fw>f)?fw:f;

  if(in[f]=='/' || in[f]=='\\')
    f++;
  return in.substr(f, r-f);
}
