/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_EXCEPTION_ID_H
#define CPROVER_CPP_EXCEPTION_ID_H

// turns a type into an exception ID

#include <util/namespace.h>
#include <util/type.h>

irep_idt cpp_exception_id(const typet &, const namespacet &);
irept cpp_exception_list(const typet &, const namespacet &);

#endif
