/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Helper functions for requiring properties of symbols

#include "require_symbol.h"

#include <testing-utils/catch.hpp>

const class_typet &require_symbol::require_complete_class(
  const symbolt &class_symbol)
{
  REQUIRE(class_symbol.is_type);

  const typet &class_symbol_type=class_symbol.type;
  REQUIRE(class_symbol_type.id()==ID_struct);

  const class_typet &class_class_type=to_class_type(class_symbol_type);
  REQUIRE(class_class_type.is_class());
  REQUIRE_FALSE(class_class_type.get_bool(ID_incomplete_class));

  return class_class_type;
}
