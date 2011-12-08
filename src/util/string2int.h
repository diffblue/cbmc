/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_STRING2INT_H
#define CPROVER_STRING2INT_H

int safe_string2int(const char *str, int base=10);
unsigned safe_string2unsigned(const char *str, int base=10);

#endif
