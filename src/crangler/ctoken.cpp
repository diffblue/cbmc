/*******************************************************************\

Module: C Token

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// ctoken

#include "ctoken.h"

#include <ostream>

void ctokent::output(std::ostream &out) const
{
  switch(kind)
  {
  case END_OF_FILE:
    out << "END_OF_FILE";
    break;
  case INT_LIT:
    out << "INT";
    break;
  case CHAR_LIT:
    out << "CHAR_LIT";
    break;
  case FLOAT_LIT:
    out << "FLOAT_LIT";
    break;
  case STRING_LIT:
    out << "STRING_LIT";
    break;
  case C_COMMENT:
    out << "C_COMMENT";
    break;
  case CPP_COMMENT:
    out << "CPP_COMMENT";
    break;
  case IDENTIFIER:
    out << "IDENTIFIER";
    break;
  case OPERATOR:
    out << "OPERATOR";
    break;
  case WS:
    out << "WS";
    break;
  case PREPROCESSOR_DIRECTIVE:
    out << "PREPROCESSOR_DIRECTIVE";
    break;
  case SEPARATOR:
    out << "SEPARATOR";
    break;
  case UNKNOWN:
    out << "UNKNOWN";
    break;
  }

  out << ' ' << text;
}

std::ostream &operator<<(std::ostream &out, const ctokent &t)
{
  t.output(out);
  return out;
}
