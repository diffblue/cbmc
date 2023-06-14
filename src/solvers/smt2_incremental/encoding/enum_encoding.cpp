// Author: Diffblue Ltd.

#include "enum_encoding.h"

#include <util/c_types.h>
#include <util/expr_cast.h>
#include <util/namespace.h>

#include <queue>

// Internal function to lower inner types of compound types (at the moment only
// arrays)
static typet encode(typet type, const namespacet &ns)
{
  std::queue<typet *> work_queue;
  work_queue.push(&type);
  while(!work_queue.empty())
  {
    typet &current = *work_queue.front();
    work_queue.pop();
    if(const auto c_enum_tag = type_try_dynamic_cast<c_enum_tag_typet>(current))
    {
      // Replace the type of the c_enum_tag with the underlying type of the enum
      // it points to
      current = ns.follow_tag(*c_enum_tag).underlying_type();
    }
    if(const auto array = type_try_dynamic_cast<array_typet>(current))
    {
      // Add the type of the array's elements to the queue to be explored
      work_queue.push(&array->element_type());
    }
  }
  return type;
}

// Worklist algorithm to lower enum types of expr and its sub-expressions.
exprt lower_enum(exprt expr, const namespacet &ns)
{
  std::queue<exprt *> work_queue;
  work_queue.push(&expr);
  while(!work_queue.empty())
  {
    exprt &current = *work_queue.front();
    work_queue.pop();

    // Replace the type of the expression node with the encoded one
    current.type() = encode(current.type(), ns);

    for(auto &operand : current.operands())
      work_queue.push(&operand);
  }
  return expr;
}
