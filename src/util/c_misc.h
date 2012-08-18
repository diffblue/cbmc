/*******************************************************************\

Module: ANSI-C Misc Utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_MISC_H
#define CPROVER_C_MISC_H

#include <string>

std::string MetaChar(char c);
void MetaString(std::string &out, const std::string &in);

#endif
