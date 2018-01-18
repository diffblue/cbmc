/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include <functional>
#include <stack>
#include <map>
#include <ostream>

#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/struct_abstract_object.h>
#include <analyses/variable-sensitivity/pointer_abstract_object.h>
#include <analyses/variable-sensitivity/array_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/ai.h>
#include <util/simplify_expr.h>

#include "abstract_enviroment.h"

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: abstract_environmentt::eval

  Inputs:
   expr - the expression to evaluate
   ns - the current namespace

 Outputs: The abstract_object representing the value of the expression

 Purpose: Evaluate the value of an expression relative to the current domain

\*******************************************************************/

abstract_object_pointert abstract_environmentt::eval(
  const exprt &expr, const namespacet &ns) const
{
  if(bottom)
    return abstract_object_factory(expr.type(), ns, false, true);

  // first try to canonicalise, including constant folding
  const exprt &simplified_expr=simplify_expr(expr, ns);

  const irep_idt simplified_id=simplified_expr.id();
  if(simplified_id==ID_symbol)
  {
    const symbol_exprt &symbol(to_symbol_expr(simplified_expr));
    const auto &symbol_entry=map.find(symbol);
    if(symbol_entry==map.cend())
    {
      return abstract_object_factory(simplified_expr.type(), ns, true);
    }
    else
    {
      abstract_object_pointert found_symbol_value=symbol_entry->second;
      return found_symbol_value;
    }
  }
  else if(simplified_id==ID_member)
  {
    member_exprt member_expr(to_member_expr(simplified_expr));

    const exprt &parent = member_expr.compound();

    abstract_object_pointert parent_abstract_object=eval(parent, ns);
    return parent_abstract_object->read(*this, member_expr, ns);
  }
  else if(simplified_id==ID_address_of)
  {
    sharing_ptrt<pointer_abstract_objectt> pointer_object=
      std::dynamic_pointer_cast<const pointer_abstract_objectt>(
        abstract_object_factory(simplified_expr.type(), simplified_expr, ns));

    // Store the abstract object in the pointer
    return pointer_object;
  }
  else if(simplified_id==ID_dereference)
  {
    dereference_exprt dereference(to_dereference_expr(simplified_expr));
    abstract_object_pointert pointer_abstract_object=
      eval(dereference.pointer(), ns);

    return pointer_abstract_object->read(*this, nil_exprt(), ns);
  }
  else if(simplified_id==ID_index)
  {
    index_exprt index_expr(to_index_expr(simplified_expr));
    abstract_object_pointert array_abstract_object=
      eval(index_expr.array(), ns);

    return array_abstract_object->read(*this, index_expr, ns);
  }
  else if(simplified_id==ID_array)
  {
    return abstract_object_factory(simplified_expr.type(), simplified_expr, ns);
  }
  else if(simplified_id==ID_constant)
  {
    return abstract_object_factory(
      simplified_expr.type(), to_constant_expr(simplified_expr), ns);
  }
  else
  {
    // No special handling required by the abstract environment
    // delegate to the abstract object
    if(simplified_expr.operands().size()>0)
    {
      return eval_expression(simplified_expr, ns);
    }
    else
    {
      // It is important that this is top as the abstract object may not know
      // how to handle the expression
      return abstract_object_factory(simplified_expr.type(), ns, true);
    }
  }
}

/*******************************************************************\

Function: abstract_environmentt::assign

  Inputs:
   expr - the expression to assign to
   value - the value to assign to the expression
   ns - the namespace

 Outputs: A boolean, true if the assignment has changed the domain.

 Purpose: Assign a value to an expression

 Assign is in principe simple, it updates the map with the new
 abstract object.  The challenge is how to handle write to compound
 objects, for example:
    a[i].x.y = 23;
 In this case we clearly want to update a, but we need to delegate to
 the object in a so that it updates the right part of it (depending on
 what kind of array abstraction it is).  So, as we find the variable
 ('a' in this case) we build a stack of which part of it is accessed.

 As abstractions may split the assignment into multiple write (for
 example pointers that could point to several locations, arrays with
 non-constant indexes), each of which has to handle the rest of the
 compound write, thus the stack is passed (to write, which does the
 actual updating) as an explicit argument rather than just via
 recursion.

 The same use case (but for the opposite reason; because you will only
 update one of the multiple objects) is also why a merge_write flag is
 needed.
\*******************************************************************/

bool abstract_environmentt::assign(
  const exprt &expr, const abstract_object_pointert value, const namespacet &ns)
{
  assert(value);

  if(value->is_bottom())
  {
    bool bottom_at_start=this->is_bottom();
    this->make_bottom();
    return !bottom_at_start;
  }

  abstract_object_pointert lhs_value=nullptr;
  // Build a stack of index, member and dereference accesses which
  // we will work through the relevant abstract objects
  exprt s = expr;
  std::stack<exprt> stactions;    // I'm not a continuation, honest guv'
  while(s.id() != ID_symbol)
  {
    if(s.id() == ID_index || s.id() == ID_member || s.id() == ID_dereference)
    {
      stactions.push(s);
      s = s.op0();
    }
    else
    {
      lhs_value=eval(s, ns);
      break;
    }
  }

  if(!lhs_value)
  {
    assert(s.id()==ID_symbol);
    const symbol_exprt &symbol_expr(to_symbol_expr(s));
    if(map.find(symbol_expr)==map.end())
    {
      lhs_value=abstract_object_factory(
        symbol_expr.type(), ns, true, false);
    }
    else
    {
      lhs_value=map[symbol_expr];
    }
  }

  abstract_object_pointert final_value;

  // This is the root abstract object that is in the map of abstract objects
  // It might not have the same type as value if the above stack isn't empty


  if(!stactions.empty())
  {
    // The symbol is not in the map - it is therefore top
    final_value=write(lhs_value, value, stactions, ns, false);
  }
  else
  {
    // If we don't have a symbol on the LHS, then we must have some expression
    // that we can write to (i.e. a pointer, an array, a struct) This appears
    // to be none of that.
    if(s.id()!=ID_symbol)
    {
      throw "invalid l-value";
    }
    // We can assign the AO directly to the symbol
    final_value=value;
  }

  const typet &lhs_type=ns.follow(lhs_value->type());
  const typet &rhs_type=ns.follow(final_value->type());

  // Write the value for the root symbol back into the map
  assert(lhs_type==rhs_type);
  // If LHS was directly the symbol
  if(s.id()==ID_symbol)
  {
    symbol_exprt symbol_expr=to_symbol_expr(s);

    if(final_value != map[symbol_expr])
    {
      map[symbol_expr]=final_value
          ->update_last_written_locations(
              value->get_last_written_locations(), false);
    }
  }
  return true;
}

/*******************************************************************\

Function: abstract_object_pointert abstract_environmentt::write

  Inputs:
   lhs - the abstract object for the left hand side of the write (i.e. the one
         to update).
   rhs - the value we are trying to write to the left hand side
   remaining_stack - what is left of the stack before the rhs can replace or be
                     merged with the rhs
   ns - the namespace
   merge_write - Are re replacing the left hand side with the right hand side
                 (e.g. we know for a fact that we are overwriting this object)
                 or could the write in fact not take place and therefore we
                 should merge to model the case where it did not.

 Outputs: A modified version of the rhs after the write has taken place

 Purpose: Write an abstract object onto another respecting a stack of
          member, index and dereference access. This ping-pongs between
          this method and the relevant write methods in abstract_struct,
          abstract_pointer and abstract_array until the stack is empty

\*******************************************************************/

abstract_object_pointert abstract_environmentt::write(
  abstract_object_pointert lhs,
  abstract_object_pointert rhs,
  std::stack<exprt> remaining_stack,
  const namespacet &ns,
  bool merge_write)
{
  assert(!remaining_stack.empty());
  const exprt & next_expr=remaining_stack.top();
  remaining_stack.pop();

  const irep_idt &stack_head_id=next_expr.id();

  // Each handler takes the abstract object referenced, copies it,
  // writes according to the type of expression (e.g. for ID_member)
  // we would (should!) have an abstract_struct_objectt which has a
  // write_member which will attempt to update the abstract object for the
  // relevant member. This modified abstract object is returned and this
  // is inserted back into the map
  if(stack_head_id==ID_index)
  {
    return lhs->write(
        *this, ns, remaining_stack, to_index_expr(next_expr), rhs, merge_write);
  }
  else if(stack_head_id==ID_member)
  {
    return lhs->write(
      *this, ns, remaining_stack, to_member_expr(next_expr), rhs, merge_write);
  }
  else if(stack_head_id==ID_dereference)
  {
    return lhs->write(
      *this, ns, remaining_stack, nil_exprt(), rhs, merge_write);
  }
  else
  {
    assert(0);
    return nullptr;
  }
}

/*******************************************************************\

Function: abstract_environmentt::assume

  Inputs:
   expr - the expression that is to be assumed
   ns - the current namespace

 Outputs: True if the assume changed the domain.

 Purpose: Reduces the domain to (an over-approximation) of the cases
          when the the expression holds.  Used to implement assume
          statements and conditional branches.

\*******************************************************************/

bool abstract_environmentt::assume(const exprt &expr, const namespacet &ns)
{
  // We should only attempt to assume Boolean things
  // This should be enforced by the well-structured-ness of the
  // goto-program and the way assume is used.

  assert(expr.type().id()==ID_bool);

  // Evaluate the expression
  abstract_object_pointert res = eval(expr, ns);

  exprt possibly_constant = res->to_constant();

  if(possibly_constant.id()!=ID_nil)  // I.E. actually a value
  {
    // Should be of the right type
    assert(possibly_constant.type().id()==ID_bool);

    if(possibly_constant.is_false())
    {
      bool currently_bottom = is_bottom();
      make_bottom();
      return !currently_bottom;
    }
  }

  /* TODO : full implementation here
   * Note that this is *very* syntax dependent so some normalisation would help
   * 1. split up conjucts, handle each part separately
   * 2. check how many variables the term contains
   *     0 = this should have been simplified away
   *    2+ = ignore as this is a non-relational domain
   *     1 = extract the expression for the variable,
   *         care must be taken for things like a[i]
   *         which can be used if i can be resolved to a constant
   * 3. use abstract_object_factory to build an abstract_objectt
   *    of the correct type (requires a little extension)
   *    This allows constant domains to handle x==23,
   *    intervals to handle x < 4, etc.
   * 4. eval the current value of the variable
   * 5. compute the meet (not merge!) of the two abstract_objectt's
   * 6. assign the new value back to the environment.
   */

  return false;
}


/*******************************************************************\

Function: abstract_environmentt::abstract_object_factory

  Inputs:
   type - the type of the object whose state should be tracked
   top - does the type of the object start as top
   bottom - does the type of the object start as bottom in the two-value domain

 Outputs: The abstract object that has been created

 Purpose: Look at the configuration for the sensitivity and create an
          appropriate abstract_object

\*******************************************************************/

abstract_object_pointert abstract_environmentt::abstract_object_factory(
  const typet &type, const namespacet &ns, bool top, bool bottom) const
{
  exprt empty_constant_expr=exprt();
  return abstract_object_factory(
    type, top, bottom, empty_constant_expr, *this, ns);
}

/*******************************************************************\

Function: abstract_environmentt::abstract_object_factory

  Inputs:
   type - the type of the object whose state should be tracked
   expr - the starting value of the symbol

 Outputs: The abstract object that has been created

 Purpose: Look at the configuration for the sensitivity and create an
          appropriate abstract_object, assigning an appropriate value

\*******************************************************************/

abstract_object_pointert abstract_environmentt::abstract_object_factory(
  const typet &type, const exprt &e, const namespacet &ns) const
{
  return abstract_object_factory(type, false, false, e, *this, ns);
}

/*******************************************************************\

Function: abstract_environmentt::abstract_object_factory

  Inputs:
   type - the type of the object whose state should be tracked
   top - does the type of the object start as top in the two-value domain
   bottom - does the type of the object start as bottom in the two-value domain
   expr - the starting value of the symbol if top and bottom are both false

 Outputs: The abstract object that has been created

 Purpose: Look at the configuration for the sensitivity and create an
          appropriate abstract_object

\*******************************************************************/

abstract_object_pointert abstract_environmentt::abstract_object_factory(
  const typet &type, bool top, bool bottom, const exprt &e,
  const abstract_environmentt &environment, const namespacet &ns) const
{
  return variable_sensitivity_object_factoryt::instance().get_abstract_object(
    type, top, bottom, e, environment, ns);
}

/*******************************************************************\

Function: abstract_environmentt::merge

  Inputs:
   env - the other environment

 Outputs: A Boolean, true when the merge has changed something

 Purpose: Computes the join between "this" and "b"

\*******************************************************************/


#include <iostream>

bool abstract_environmentt::merge(const abstract_environmentt &env)
{
  // Use the sharing_map's "iterative over all differences" functionality
  // This should give a significant performance boost
  // We can strip down to just the things that are in both

  // for each entry in the incoming environment we need to either add it
  // if it is new, or merge with the existing key if it is not present

  if(bottom)
  {
    *this=env;
    return !env.bottom;
  }
  else if(env.bottom)
  {
    return false;
  }
  else
  {
    // For each element in the intersection of map and env.map merge
    // If the result of the merge is top, remove from the map
    bool modified=false;
    for(const auto &entry : env.map)
    {
      if(map.find(entry.first)!=map.end())
      {
        bool object_modified=false;
        abstract_object_pointert new_object=
          abstract_objectt::merge(
            map[entry.first],
            entry.second,
            object_modified);

        modified|=object_modified;
        map[entry.first]=new_object;

        // Write, even if TOP. Since we now track the write locations of an
        // object, even if it is TOP we still have useful information about it.
        // This is used for when we want to find out what has been modified
        // between two locations (even if we don't know what has been written).
      }
      else
      {
        // Map doesn't contain key so the resulting map shouldn't either
      }
    }

    // Keep TOP items too.

    return modified;
  }
}

/*******************************************************************\

Function: abstract_environmentt::havoc

  Inputs:
   havoc_string - diagnostic string to track down havoc causing.

 Outputs: None

 Purpose: Set the domain to top

\*******************************************************************/

void abstract_environmentt::havoc(const std::string &havoc_string)
{
  // TODO(tkiley): error reporting
  make_top();
}

/*******************************************************************\

Function: abstract_environmentt::make_top

  Inputs: None

 Outputs: None

 Purpose: Set the domain to top

\*******************************************************************/

void abstract_environmentt::make_top()
{
  // since we assume anything is not in the map is top this is sufficient
  map.clear();
  bottom=false;
}

/*******************************************************************\

Function: abstract_environmentt::make_bottom

  Inputs: None

 Outputs: None

 Purpose: Set the domain to top

\*******************************************************************/

void abstract_environmentt::make_bottom()
{
  map.clear();
  bottom=true;
}

/*******************************************************************\

Function: abstract_environmentt::is_bottom

  Inputs:

 Outputs:

 Purpose: Gets whether the domain is bottom

\*******************************************************************/

bool abstract_environmentt::is_bottom() const
{
  return map.empty() && bottom;
}

/*******************************************************************\

Function: abstract_environmentt::is_top

  Inputs:

 Outputs:

 Purpose: Gets whether the domain is top

\*******************************************************************/

bool abstract_environmentt::is_top() const
{
  return map.empty() && !bottom;
}

/*******************************************************************\

Function: abstract_environmentt::output

  Inputs:
   out - the stream to write to
   ai - the abstract interpreter that contains this domain
   ns - the current namespace

 Outputs: None

 Purpose: Print out all the values in the abstract object map

\*******************************************************************/

void abstract_environmentt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  out << "{\n";

  for(const auto &entry : map)
  {
    out << entry.first.get_identifier()
        << " (" << ") -> ";
    entry.second->output(out, ai, ns);

    out << " @ ";
    entry.second->output_last_written_locations(
        out, entry.second->get_last_written_locations());
    out << "\n";
  }
  out << "}\n";
}

/*******************************************************************\

Function: abstract_environmentt::verify

  Inputs:

 Outputs:

 Purpose: Check there aren't any null pointer mapped values

\*******************************************************************/

bool abstract_environmentt::verify() const
{
  for(const auto &entry : map)
  {
    if(!entry.second)
    {
      return false;
    }
  }
  return true;
}

abstract_object_pointert abstract_environmentt::eval_expression(
  const exprt &e, const namespacet &ns) const
{
  // Delegate responsibility of resolving to a boolean abstract object
  // to the abstract object being compared against
  abstract_object_pointert eval_obj=abstract_object_factory(e.type(), e, ns);
  return eval_obj->expression_transform(e, *this, ns);
}

/*******************************************************************\

Function: abstract_environmentt::erase

  Inputs:  A symbol to delete from the map

 Outputs:

 Purpose:  Delete a symbol from the map.  This is necessary if the
           symbol falls out of scope and should no longer be tracked.

\*******************************************************************/

void abstract_environmentt::erase(const symbol_exprt &expr)
{
    map.erase(expr);
}

/*******************************************************************\

Function: abstract_environmentt::environment_diff

  Inputs:  Two abstract_environmentt's that need to be intersected for,
           so that we can find symbols that have changed between
           different domains.

 Outputs:  An std::vector containing the symbols that are present in
           both environments.

 Purpose:  For our implementation of variable sensitivity domains, we
           need to be able to efficiently find symbols that have changed
           between different domains. To do this, we need to be able
           to quickly find which symbols have new written locations,
           which we do by finding the intersection between two different
           domains (environments).

\*******************************************************************/

std::vector<symbol_exprt> abstract_environmentt::modified_symbols(
  const abstract_environmentt &first, const abstract_environmentt &second)
{
  // Find all symbols who have different write locations in each map
  std::vector<symbol_exprt> symbols_diff;
  for (const auto &entry : first.map)
  {
    const auto &second_entry = second.map.find(entry.first);
    if (second_entry != second.map.end())
    {
      // for the last written write locations to match
      // each location in one must be equal to precisely one location
      // in the other
      // Since a set can assume at most one match

      const abstract_objectt::locationst &first_write_locations=
        entry.second->get_last_written_locations();
      const abstract_objectt::locationst &second_write_locations=
        second_entry->second->get_last_written_locations();

      class location_ordert
      {
      public:
        bool operator()(
          goto_programt::const_targett instruction,
          goto_programt::const_targett other_instruction)
        {
          return instruction->location_number>
            other_instruction->location_number;
        }
      };

      typedef std::set<goto_programt::const_targett, location_ordert>
        sorted_locationst;

      sorted_locationst lhs_location;
      for(const auto &entry:first_write_locations)
      {
        lhs_location.insert(entry);
      }


      sorted_locationst rhs_location;
      for(const auto &entry:second_write_locations)
      {
        rhs_location.insert(entry);
      }

      abstract_objectt::locationst intersection;
      std::set_intersection(
        lhs_location.cbegin(),
        lhs_location.cend(),
        rhs_location.cbegin(),
        rhs_location.cend(),
        std::inserter(intersection, intersection.end()),
        location_ordert());
      bool all_matched=intersection.size()==first_write_locations.size() &&
        intersection.size()==second_write_locations.size();

      if (!all_matched)
      {
        symbols_diff.push_back(entry.first);
      }
    }
  }

  // Add any symbols that are only in the second map
  for(const auto &entry : second.map)
  {
    const auto &second_entry = first.map.find(entry.first);
    if (second_entry==first.map.end())
    {
      symbols_diff.push_back(entry.first);
    }
  }
  return symbols_diff;
}
