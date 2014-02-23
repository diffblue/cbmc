/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_STRING2INT_H
#define CPROVER_STRING2INT_H

#include <string>

// These check that the string is indeed a valid number,
// and fail an assertion otherwise.
int safe_str2int(const char *str, int base=10);
unsigned safe_str2unsigned(const char *str, int base=10);

int safe_string2int(const std::string &str, int base=10);
unsigned safe_string2unsigned(const std::string &str, int base=10);

// These mimick atoi/atol: any errors are silently ignored.
// They are meant to replace atoi/atol.
int unsafe_str2int(const char *str, int base=10);
unsigned unsafe_str2unsigned(const char *str, int base=10);

int unsafe_string2int(const std::string &str, int base=10);
unsigned unsafe_string2unsigned(const std::string &str, int base=10);

#endif
