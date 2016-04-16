/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cctype>

#include <util/string2int.h>
#include <util/parser.h>

#include "literals/unescape_string.h"
#include "preprocessor_line.h"

/*******************************************************************\

Function: preprocessor_line

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void preprocessor_line(
  const char *text,
  parsert &parser)
{
  const char *ptr=text;
  std::string line_number;
  
  // skip WS
  while(*ptr==' ' || *ptr=='\t') ptr++;

  // skip #
  if(*ptr!='#') return;
  ptr++;

  // skip WS
  while(*ptr==' ' || *ptr=='\t') ptr++;

  // skip "line"
  if(*ptr=='l')
  {
    while(*ptr!=0 && *ptr!=' ' && *ptr!='\t') ptr++;
  }

  // skip WS
  while(*ptr==' ' || *ptr=='\t') ptr++;

  // get line number
  while(isdigit(*ptr))
  {
    line_number+=*ptr;
    ptr++;
  }
  
  // skip until "
  while(*ptr!='\n' && *ptr!='"') ptr++;

  parser.set_line_no(unsafe_string2unsigned(line_number));

  // skip "
  if(*ptr!='"')
    return;
  
  ptr++;
  
  std::string file_name_tmp;

  // get file name
  while(*ptr!='\n' && *ptr!='"')
  {
    file_name_tmp+=*ptr;
    ptr++;
  }

  std::string file_name_tmp2;
  unescape_string(file_name_tmp, file_name_tmp2);
  parser.set_file(file_name_tmp2);

  // GCC provides further information
  // https://gcc.gnu.org/onlinedocs/cpp/Preprocessor-Output.html
  if(*ptr=='"') ++ptr;
  while(*ptr!='\n')
  {
    // skip WS
    while(*ptr==' ' || *ptr=='\t') ++ptr;
    if(!isdigit(*ptr))
      break;

    std::string flag_str;
    while(isdigit(*ptr))
    {
      flag_str+=*ptr;
      ++ptr;
    }

    unsigned flag=safe_string2unsigned(flag_str);

    switch(flag)
    {
      case 1:
        // opening a new file -- covered by parser.set_file
        break;
      case 2:
        // return from included file -- ignored
        break;
      case 3:
        parser.set_is_system_header();
        break;
      case 4:
        // extern "C" -- ignored;
        break;
      default:
        assert(false);
    }
  }
}
