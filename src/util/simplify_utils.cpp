/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_utils.h"
#include "as_const.h"

#include <algorithm>

/// sort operands of an expression according to ordering defined by operator<
/// \par parameters: operand list
/// \return modifies operand list returns true iff nothing was changed
bool sort_operands(exprt::operandst &operands)
{
  bool do_sort=false;

  forall_expr(it, operands)
  {
    exprt::operandst::const_iterator next_it=it;
    next_it++;

    if(next_it!=operands.end() && *next_it < *it)
    {
      do_sort=true;
      break;
    }
  }

  if(!do_sort)
    return true;

  std::sort(operands.begin(), operands.end());

  return false;
}

/// produce canonical ordering for associative and commutative binary operators
// The entries
//  { ID_plus,   ID_floatbv  },
//  { ID_mult,   ID_floatbv  },
//  { ID_plus,   ID_pointer  },
// are deliberately missing, as FP-addition and multiplication
// aren't associative. Addition to pointers isn't really
// associative.

struct saj_tablet
{
  const irep_idt id;
  const irep_idt type_ids[10];
} const saj_table[]=
{
  { ID_plus,  {ID_integer    ,
               ID_natural    ,
               ID_real       ,
               ID_complex    ,
               ID_rational   ,
               ID_unsignedbv ,
               ID_signedbv   ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_mult,  {ID_integer    ,
               ID_natural    ,
               ID_real       ,
               ID_complex    ,
               ID_rational   ,
               ID_unsignedbv ,
               ID_signedbv   ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_and,   {ID_bool       ,
               irep_idt()  }},
  { ID_or,    {ID_bool       ,
               irep_idt()  }},
  { ID_xor,   {ID_bool       ,
               irep_idt()  }},
  { ID_bitand, {ID_unsignedbv ,
               ID_signedbv   ,
               ID_floatbv    ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_bitor, {ID_unsignedbv ,
               ID_signedbv   ,
               ID_floatbv    ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_bitxor, {ID_unsignedbv ,
               ID_signedbv   ,
               ID_floatbv    ,
               ID_fixedbv    ,
               irep_idt()  }},
  { irep_idt(), { irep_idt() }}
};

static bool sort_and_join(
  const struct saj_tablet &saj_entry,
  const irep_idt &type_id)
{
  for(unsigned i=0; !saj_entry.type_ids[i].empty(); i++)
    if(type_id==saj_entry.type_ids[i])
      return true;

  return false;
}

static const struct saj_tablet &sort_and_join(
  const irep_idt &id,
  const irep_idt &type_id)
{
  unsigned i=0;

  for( ; !saj_table[i].id.empty(); i++)
    if(id==saj_table[i].id &&
       sort_and_join(saj_table[i], type_id))
      return saj_table[i];

  return saj_table[i];
}

bool sort_and_join(exprt &expr)
{
  bool no_change = true;

  if(!expr.has_operands())
    return true;

  const struct saj_tablet &saj_entry =
    sort_and_join(expr.id(), as_const(expr).type().id());
  if(saj_entry.id.empty())
    return true;

  // check operand types

  forall_operands(it, expr)
    if(!sort_and_join(saj_entry, it->type().id()))
      return true;

  // join expressions

  exprt::operandst new_ops;
  new_ops.reserve(expr.operands().size());

  forall_operands(it, expr)
  {
    if(it->id()==expr.id())
    {
      new_ops.reserve(new_ops.capacity()+it->operands().size()-1);

      forall_operands(it2, *it)
        new_ops.push_back(*it2);

      no_change = false;
    }
    else
      new_ops.push_back(*it);
  }

  // sort it

  no_change = sort_operands(new_ops) && no_change;
  expr.operands().swap(new_ops);

  return no_change;
}
