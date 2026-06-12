/*******************************************************************\

Module: C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C Language Conversion

#include "convert_character_literal.h"

#include <climits>

#include <util/arith_tools.h>
#include <util/c_types.h>

#include "unescape_string.h"

exprt convert_character_literal(
  const std::string &src,
  bool force_integer_type,
  const source_locationt &source_location)
{
  PRECONDITION(src.size() >= 2);

  exprt result;

  if(src[0]=='L' || src[0]=='u' || src[0]=='U')
  {
    // u8 prefix: char8_t (unsigned char) in C++20
    if(src[0] == 'u' && src.size() >= 3 && src[1] == '8')
    {
      PRECONDITION(src[2] == '\'');
      PRECONDITION(src[src.size() - 1] == '\'');

      std::basic_string<char32_t> value =
        unescape_wide_string(std::string(src, 3, src.size() - 4));
      CHECK_RETURN(!value.empty());

      result = from_integer(value[0], unsigned_char_type());
      result.add_source_location() = source_location;
      return result;
    }

    PRECONDITION(src[1] == '\'');
    PRECONDITION(src[src.size() - 1] == '\'');

    std::basic_string<char32_t> value =
      unescape_wide_string(std::string(src, 2, src.size() - 3));
    // the parser rejects empty character constants
    CHECK_RETURN(!value.empty());

    // L is wchar_t, u is char16_t, U is char32_t ([lex.ccon]).
    typet type;
    if(src[0] == 'L')
      type = wchar_t_type();
    else if(src[0] == 'u')
      type = char16_t_type();
    else
    {
      PRECONDITION(src[0] == 'U');
      type = char32_t_type();
    }

    if(value.size() == 1)
    {
      result=from_integer(value[0], type);
    }
    else if(value.size()>=2 && value.size()<=4)
    {
      // TODO: need to double-check. GCC seems to say that each
      // character is wchar_t wide.
      mp_integer x=0;

      for(unsigned i=0; i<value.size(); i++)
      {
        mp_integer z=(unsigned char)(value[i]);
        z = z << ((value.size() - i - 1) * CHAR_BIT);
        x+=z;
      }

      // use the prefix-selected wide type (L: wchar_t, u: char16_t,
      // U: char32_t)
      result=from_integer(x, type);
    }
    else
      throw invalid_source_file_exceptiont{
        "wide literals with " + std::to_string(value.size()) +
          " characters are not supported",
        source_location};
  }
  else
  {
    PRECONDITION(src[0] == '\'');
    PRECONDITION(src[src.size() - 1] == '\'');

    std::string value=
      unescape_string(std::string(src, 1, src.size()-2));
    // the parser rejects empty character constants
    CHECK_RETURN(!value.empty());

    if(value.size() == 1)
    {
      typet type=force_integer_type?signed_int_type():char_type();
      result=from_integer(value[0], type);
    }
    else if(value.size()>=2 && value.size()<=4)
    {
      mp_integer x=0;

      for(unsigned i=0; i<value.size(); i++)
      {
        mp_integer z=(unsigned char)(value[i]);
        z = z << ((value.size() - i - 1) * CHAR_BIT);
        x+=z;
      }

      // always integer, never char!
      result=from_integer(x, signed_int_type());
    }
    else
      throw invalid_source_file_exceptiont{
        "literals with " + std::to_string(value.size()) +
          " characters are not supported",
        source_location};
  }

  result.add_source_location() = source_location;
  return result;
}
