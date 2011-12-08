/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_STRING2INT_H
#define CPROVER_STRING2INT_H

#include <string>

int safe_str2int(const char *str, int base=10);
unsigned safe_str2unsigned(const char *str, int base=10);

int safe_string2int(const std::string &str, int base=10);
unsigned safe_string2unsigned(const std::string &str, int base=10);

#endif
