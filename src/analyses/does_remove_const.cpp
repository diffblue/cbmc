/*******************************************************************\

 Module: Analyses

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <goto-programs/goto_program.h>
#include <util/type.h>
#include <util/expr.h>
#include <util/std_code.h>
#include <util/base_type.h>
#include <ansi-c/c_qualifiers.h>

#include "does_remove_const.h"

/*******************************************************************\

Function: does_remove_constt::does_remove_constt

  Inputs:
   goto_program - the goto program to check
   ns - the namespace of the goto program (used for checking type equality)

 Outputs:

 Purpose: A naive analysis to look for casts that remove const-ness from
          pointers.

\*******************************************************************/

does_remove_constt::does_remove_constt(
  const goto_programt &goto_program,
  const namespacet &ns):
    goto_program(goto_program),
    ns(ns)
{}

/*******************************************************************\

Function: does_remove_constt::operator()

  Inputs:

 Outputs: Returns true if the program contains a const-removing cast

 Purpose: A naive analysis to look for casts that remove const-ness from
          pointers.

\*******************************************************************/

bool does_remove_constt::operator()() const
{
  for(const goto_programt::instructiont &instruction :
    goto_program.instructions)
  {
    if(instruction.is_assign())
    {
      const code_assignt assign=to_code_assign(instruction.code);
      const typet &rhs_type=assign.rhs().type();
      const typet &lhs_type=assign.lhs().type();

      // Compare the types recursively for a point where the rhs is more
      // const that the lhs
      if(!is_type_at_least_as_const_as(lhs_type, rhs_type))
      {
        return true;
      }

      bool sub_expr_lose_const=does_expr_lose_const(assign.rhs());
      if(sub_expr_lose_const)
      {
        return true;
      }
    }
  }

  return false;
}

/*******************************************************************\

Function: does_remove_constt::does_expr_lose_const()

  Inputs:
   expr - The expression to check

 Outputs: Returns true if somewhere in the passed expression tree the const-ness
          is lost.

 Purpose: Search the expression tree to look for any children that have the
          same base type, but a less strict const qualification.
          If one is found, we return true.

\*******************************************************************/

bool does_remove_constt::does_expr_lose_const(const exprt &expr) const
{
  const typet &root_type=expr.type();

  // Look in each child that has the same base type as the root
  for(const exprt &op : expr.operands())
  {
    const typet &op_type=op.type();
    if(base_type_eq(op_type, root_type, ns))
    {
      // Is this child more const-qualified than the root
      if(!is_type_at_least_as_const_as(root_type, op_type))
      {
        return true;
      }
    }

    // Recursively check the children of this child
    if(does_expr_lose_const(op))
    {
      return true;
    }
  }
  return false;
}

/*******************************************************************\

Function: does_remove_constt::is_type_at_least_as_const_as

  Inputs:
   type_more_const - the type we are expecting to be at least as const qualified
   type_compare - the type we are comparing against which may be less const
                  qualified

 Outputs: Returns true if type_more_const is at least as const as type_compare

 Purpose: A recursive check to check the type_more_const is at least as const
          as type compare.

          type_more_const | type_compare || result
          ----------------------------------------
          const int *     | const int *  -> true
          int *           | const int *  -> false
          const int *     | int *        -> true
          int *           | int * const  -> false

\*******************************************************************/

bool does_remove_constt::is_type_at_least_as_const_as(
  typet type_more_const, typet type_compare) const
{
  while(!type_compare.id().empty() && !type_more_const.id().empty())
  {
    const c_qualifierst rhs_qualifiers(type_compare);
    const c_qualifierst lhs_qualifiers(type_more_const);
    if(rhs_qualifiers.is_constant && !lhs_qualifiers.is_constant)
    {
      return false;
    }

    type_compare=type_compare.subtype();
    type_more_const=type_more_const.subtype();
  }

  // Both the types should have the same number of subtypes
  assert(type_compare.id().empty() && type_more_const.id().empty());
  return true;
}
