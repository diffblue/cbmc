/*******************************************************************\

Module: util

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_UNWRAP_NESTED_EXCEPTION_H
#define CPROVER_UTIL_UNWRAP_NESTED_EXCEPTION_H

#include <exception>
#include <string>

std::string unwrap_exception(const std::exception &e, int level = 0);

#endif // CPROVER_UTIL_UNWRAP_NESTED_EXCEPTION_H
