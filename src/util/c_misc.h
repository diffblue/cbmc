/*******************************************************************\

Module: ANSI-C Misc Utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_MISC_H
#define CPROVER_C_MISC_H

#include <string>

void MetaChar(std::string &out, char c, bool inString);
void MetaString(std::string &out, const std::string &in);

#endif
