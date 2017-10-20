/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Helper functions for requiring specific types
/// If the type is of the wrong type, throw a CATCH exception
/// Also checks associated properties and returns a casted version of the
/// expression.

#ifndef CPROVER_TESTING_UTILS_REQUIRE_TYPE_H
#define CPROVER_TESTING_UTILS_REQUIRE_TYPE_H

#include <util/optional.h>
#include <util/std_types.h>

// NOLINTNEXTLINE(readability/namespace)
namespace require_type
{
pointer_typet
require_pointer(const typet &type, const optionalt<typet> &subtype);

struct_typet::componentt require_component(
  const struct_typet &struct_type,
  const irep_idt &component_name);
}

#endif
