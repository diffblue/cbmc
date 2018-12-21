/*******************************************************************\

Module: Analyses

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Analyses

#include "does_remove_const.h"

#include <goto-programs/goto_program.h>
#include <util/type.h>
#include <util/expr.h>
#include <util/std_code.h>
#include <util/base_type.h>

/// A naive analysis to look for casts that remove const-ness from pointers.
/// \param goto_program: the goto program to check
/// \param ns: the namespace of the goto program (used for checking type
///   equality)
does_remove_constt::does_remove_constt(
  const goto_programt &goto_program,
  const namespacet &ns):
    goto_program(goto_program),
    ns(ns)
{}

/// A naive analysis to look for casts that remove const-ness from pointers.
/// \return Returns true if the program contains a const-removing cast
std::pair<bool, source_locationt> does_remove_constt::operator()() const
{
  for(const goto_programt::instructiont &instruction :
    goto_program.instructions)
  {
    if(!instruction.is_assign())
    {
      continue;
    }

    const code_assignt &assign=to_code_assign(instruction.code);
    const typet &rhs_type=assign.rhs().type();
    const typet &lhs_type=assign.lhs().type();

    // Compare the types recursively for a point where the rhs is more
    // const that the lhs
    if(!does_type_preserve_const_correctness(&lhs_type, &rhs_type))
    {
      return {true, assign.find_source_location()};
    }

    if(does_expr_lose_const(assign.rhs()))
    {
      return {true, assign.rhs().find_source_location()};
    }
  }

  return {false, source_locationt()};
}

/// Search the expression tree to look for any children that have the same base
/// type, but a less strict const qualification. If one is found, we return
/// true.
/// \param expr: The expression to check
/// \return Returns true if somewhere in the passed expression tree the const-
///   ness is lost.
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
      if(!does_type_preserve_const_correctness(&root_type, &op_type))
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

/// A recursive check that handles when assigning a source value to a target, is
/// the assignment a loss of const-correctness.
///
/// For primitive types, it always returns true since these are copied
///
/// For pointers we requires that if in the source it's value couldn't
/// be modified, then it still can't be modified in the target
///
/// target_type     | source_type  || result
/// ----------------------------------------
/// const int       | int          -> true
/// int             | const int    -> true
/// const int       | const int    -> true
/// int             | int          -> true
///
/// int *           | int * const  -> true
/// int *           | const int *  -> false
/// const int *     | int *        -> true
/// const int *     | const int *  -> true
/// int * const     | int *        -> true
///
/// See unit/analyses/does_type_preserve_const_correcness for
/// comprehensive list
/// \param target_type: the resulting type
/// \param source_type: the starting type
/// \return Returns true if a value of type source_type could be assigned into a
///   a value of target_type without losing const-correctness
bool does_remove_constt::does_type_preserve_const_correctness(
  const typet *target_type, const typet *source_type) const
{
  while(target_type->id()==ID_pointer)
  {
    bool direct_subtypes_at_least_as_const=
      is_type_at_least_as_const_as(
        target_type->subtype(), source_type->subtype());
    // We have a pointer to something, but the thing it is pointing to can't be
    // modified normally, but can through this pointer
    if(!direct_subtypes_at_least_as_const)
      return false;
    // Check the subtypes if they are pointers
    target_type=&target_type->subtype();
    source_type=&source_type->subtype();
  }
  return true;
}

/// A simple check to check the type_more_const is at least as const as type
/// compare. This only checks the exact type, use
/// `is_pointer_at_least_as_constant_as` for dealing with nested types
///
/// type_more_const | type_compare || result
/// ----------------------------------------
/// const int       | int          -> true
/// int             | const int    -> false
/// const int       | const int    -> true
/// int             | int          -> true
/// int *           | int * const  -> false
/// int *           | const int *  -> true
/// const int *     | int *        -> true
/// int * const     | int *        -> true
///
/// See unit/analyses/is_type_as_least_as_const_as for comprehensive list
/// \param type_more_const: the type we are expecting to be at least as const
///   qualified
/// \param type_compare: the type we are comparing against which may be less
///   const qualified
/// \return Returns true if type_more_const is at least as const as type_compare
bool does_remove_constt::is_type_at_least_as_const_as(
  const typet &type_more_const, const typet &type_compare) const
{
  return !type_compare.get_bool(ID_C_constant) ||
         type_more_const.get_bool(ID_C_constant);
}
