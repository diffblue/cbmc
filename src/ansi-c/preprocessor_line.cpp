/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdlib.h>
#include <ctype.h>

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
  unsigned &line_no,
  irep_idt &file_name)
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

  line_no=atoi(line_number.c_str());

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
  file_name=file_name_tmp2;
}
