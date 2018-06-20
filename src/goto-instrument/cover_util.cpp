/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Coverage Instrumentation Utilities

#include "cover_util.h"

bool is_condition(const exprt &src)
{
  if(src.type().id() != ID_bool)
    return false;

  // conditions are 'atomic predicates'
  if(
    src.id() == ID_and || src.id() == ID_or || src.id() == ID_not ||
    src.id() == ID_implies)
    return false;

  return true;
}

void collect_conditions_rec(const exprt &src, std::set<exprt> &dest)
{
  if(src.id() == ID_address_of)
  {
    return;
  }

  for(const auto &op : src.operands())
    collect_conditions_rec(op, dest);

  if(is_condition(src) && !src.is_constant())
    dest.insert(src);
}

std::set<exprt> collect_conditions(const exprt &src)
{
  std::set<exprt> result;
  collect_conditions_rec(src, result);
  return result;
}

std::set<exprt> collect_conditions(const goto_programt::const_targett t)
{
  switch(t->type)
  {
  case GOTO:
  case ASSERT:
    return collect_conditions(t->guard);

  case ASSIGN:
  case FUNCTION_CALL:
    return collect_conditions(t->code);

  case CATCH:
  case THROW:
  case DEAD:
  case DECL:
  case RETURN:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case START_THREAD:
  case END_THREAD:
  case END_FUNCTION:
  case LOCATION:
  case OTHER:
  case SKIP:
  case ASSUME:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    break;
  }

  return std::set<exprt>();
}

void collect_operands(const exprt &src, std::vector<exprt> &dest)
{
  for(const exprt &op : src.operands())
  {
    if(op.id() == src.id())
      collect_operands(op, dest);
    else
      dest.push_back(op);
  }
}

void collect_decisions_rec(const exprt &src, std::set<exprt> &dest)
{
  if(src.id() == ID_address_of)
  {
    return;
  }

  if(src.type().id() == ID_bool)
  {
    if(src.is_constant())
    {
      // ignore me
    }
    else if(src.id() == ID_not)
    {
      collect_decisions_rec(src.op0(), dest);
    }
    else
    {
      dest.insert(src);
    }
  }
  else
  {
    for(const auto &op : src.operands())
      collect_decisions_rec(op, dest);
  }
}

std::set<exprt> collect_decisions(const exprt &src)
{
  std::set<exprt> result;
  collect_decisions_rec(src, result);
  return result;
}

std::set<exprt> collect_decisions(const goto_programt::const_targett t)
{
  switch(t->type)
  {
  case GOTO:
  case ASSERT:
    return collect_decisions(t->guard);

  case ASSIGN:
  case FUNCTION_CALL:
    return collect_decisions(t->code);

  case CATCH:
  case THROW:
  case DEAD:
  case DECL:
  case RETURN:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case START_THREAD:
  case END_THREAD:
  case END_FUNCTION:
  case LOCATION:
  case OTHER:
  case SKIP:
  case ASSUME:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    break;
  }

  return std::set<exprt>();
}
