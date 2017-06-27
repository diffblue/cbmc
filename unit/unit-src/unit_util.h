/*******************************************************************\

 Module: Unit Test Utility Functions

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#ifndef CPROVER_UNIT_SRC_UNIT_UTIL_H
#define CPROVER_UNIT_SRC_UNIT_UTIL_H

#include <ostream>
#include <util/irep.h>

/// For printing irept data structures when used inside the unit tests
/// (e.g. for INFO, REQUIRE etc macros
/// \param os: The ostream to write to
/// \param value: The irept data structure to print
/// \returns The ostream after writing to it
std::ostream &operator<<(std::ostream &os, const irept &value);

#endif // CPROVER_UNIT_SRC_UNIT_UTIL_H
