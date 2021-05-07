/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_EXCEPTION_ID_H
#define CPROVER_CPP_CPP_EXCEPTION_ID_H

#include <util/irep.h>

class namespacet;
class typet;

// turns a type into an exception ID

irep_idt cpp_exception_id(const typet &, const namespacet &);
irept cpp_exception_list(const typet &, const namespacet &);

#endif // CPROVER_CPP_CPP_EXCEPTION_ID_H
