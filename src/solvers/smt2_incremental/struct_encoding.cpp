// Author: Diffblue Ltd.

#include "struct_encoding.h"

#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/make_unique.h>

#include <solvers/flattening/boolbv_width.h>

#include <queue>

struct_encodingt::struct_encodingt(const namespacet &ns)
  : boolbv_width{util_make_unique<boolbv_widtht>(ns)}
{
}

struct_encodingt::struct_encodingt(const struct_encodingt &other)
  : boolbv_width{util_make_unique<boolbv_widtht>(*other.boolbv_width)}
{
}

struct_encodingt::~struct_encodingt() = default;

typet struct_encodingt::encode(typet type) const
{
  std::queue<typet *> work_queue;
  work_queue.push(&type);
  while(!work_queue.empty())
  {
    typet &current = *work_queue.front();
    work_queue.pop();
    if(const auto struct_tag = type_try_dynamic_cast<struct_tag_typet>(current))
    {
      const auto width = (*boolbv_width)(*struct_tag);
      if(width == 0)
        UNIMPLEMENTED_FEATURE("support for zero bit width structs.");
      current = bv_typet{width};
    }
    if(const auto array = type_try_dynamic_cast<array_typet>(current))
    {
      work_queue.push(&array->element_type());
    }
  }
  return type;
}

static exprt encode(const struct_exprt &struct_expr)
{
  INVARIANT(
    !struct_expr.operands().empty(),
    "empty structs may not be encoded into SMT terms.");
  if(struct_expr.operands().size() == 1)
    return struct_expr.operands().front();
  return concatenation_exprt{struct_expr.operands(), struct_expr.type()};
}

exprt struct_encodingt::encode(exprt expr) const
{
  std::queue<exprt *> work_queue;
  work_queue.push(&expr);
  while(!work_queue.empty())
  {
    exprt &current = *work_queue.front();
    work_queue.pop();
    current.type() = encode(current.type());
    if(const auto struct_expr = expr_try_dynamic_cast<struct_exprt>(current))
      current = ::encode(*struct_expr);
    for(auto &operand : current.operands())
      work_queue.push(&operand);
  }
  return expr;
}
