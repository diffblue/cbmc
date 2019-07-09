/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#include "convert_string_value.h"

string_constantt convert_identifier(const std::string &src)
{
  string_constantt result{src};
  result.set(ID_statement_list_type, ID_statement_list_identifier);
  return result;
}

string_constantt convert_title(const std::string &src)
{
  string_constantt result{src};
  result.set(ID_statement_list_type, ID_statement_list_title);
  return result;
}

string_constantt convert_version(const std::string &src)
{
  string_constantt result{src};
  result.set(ID_statement_list_type, ID_statement_list_version);
  return result;
}

code_labelt convert_label(const std::string &src)
{
  // Cut the trailing colon
  std::string value = src.substr(0, src.length() - 1);

  return code_labelt{value, codet(ID_label)};
}
