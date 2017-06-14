/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <ostream>

#include "cpp_namespace_spec.h"
#include "cpp_item.h"

void cpp_namespace_spect::output(std::ostream &out) const
{
  out << "  namespace: " << get_namespace() << "\n";
}
