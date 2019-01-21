/********************************************************************\

Module: Type for string expressions used by the string solver.
        These string expressions contain a field `length`, of type
        `index_type`, a field `content` of type `content_type`.
        This module also defines functions to recognise the C and java
        string types.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Type for string expressions used by the string solver. These string
///   expressions contain a field `length`, of type `index_type`, a field
///   `content` of type `content_type`. This module also defines functions to
///   recognise the C and java string types.

#include "refined_string_type.h"

#include "std_expr.h"

refined_string_typet::refined_string_typet(
  const typet &index_type,
  const pointer_typet &content_type)
  : struct_typet({{"length", index_type}, {"content", content_type}})
{
  set_tag(CPROVER_PREFIX"refined_string_type");
}
