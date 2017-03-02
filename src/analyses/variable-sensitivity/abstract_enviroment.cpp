/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include "abstract_enviroment.h"
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
  if (is_bottom)
    return abstract_object_factory(expr.type(), ns, false, true);

  typedef std::function<abstract_object_pointert(const exprt &)> eval_handlert;
  std::map<irep_idt, eval_handlert> handlers=
  {
    {
      ID_symbol, [&](const exprt &expr)
      {
        const symbol_exprt &symbol(to_symbol_expr(expr));
        const auto &symbol_entry=map.find(symbol);
        if(symbol_entry==map.cend())
        {
          return abstract_object_factory(expr.type(), ns, true);
        }
        else
        {
          return symbol_entry->second;
        }
      }
    },
    {
      ID_constant, [&](const exprt &expr)
      {
        return abstract_object_factory(
          expr.type(), to_constant_expr(expr), ns);
      }
    },
    {
      ID_member, [&](const exprt &expr)
      {
        member_exprt member_expr(to_member_expr(expr));
        sharing_ptrt<struct_abstract_objectt> struct_abstract_object=
          std::dynamic_pointer_cast<struct_abstract_objectt>(
            eval(member_expr.compound(), ns));

        return struct_abstract_object->read_component(*this, member_expr, ns);
      }
    },
    {
      ID_address_of, [&](const exprt &expr)
      {
        sharing_ptrt<pointer_abstract_objectt> pointer_object=
          std::dynamic_pointer_cast<pointer_abstract_objectt>(
            abstract_object_factory(expr.type(), expr, ns));

        // Store the abstract object in the pointer
        return pointer_object;
      }
    },
    {
      ID_dereference, [&](const exprt &expr)
      {
        dereference_exprt dereference(to_dereference_expr(expr));
        sharing_ptrt<pointer_abstract_objectt> pointer_abstract_object=
          std::dynamic_pointer_cast<pointer_abstract_objectt>(
            eval(dereference.pointer(), ns));

        return pointer_abstract_object->read_dereference(*this, ns);
      }
    },
    {
      ID_index, [&](const exprt &expr)
      {
        index_exprt index_expr(to_index_expr(expr));
        sharing_ptrt<array_abstract_objectt> array_abstract_object=
          std::dynamic_pointer_cast<array_abstract_objectt>(
            eval(index_expr.array(), ns));

        return array_abstract_object->read_index(*this, index_expr, ns);
      }
    }
  };

  // first try to canonicalise, including constant folding
  const exprt &simplified_expr=simplify_expr(expr, ns);

  const auto &handler=handlers.find(simplified_expr.id());
  if(handler==handlers.cend())
  {
    // No special handling required by the abstract environment
    // delegate to the abstract object
    if(simplified_expr.operands().size()>0)
    {
      return eval_expression(simplified_expr, ns);
    }
    else
    {
      return abstract_object_factory(simplified_expr.type(), ns, true);
    }
  }
  else
  {
    return handler->second(simplified_expr);
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

  // Build a stack of index, member and dereference accesses which
  // we will work through the relevant abstract objects
  exprt s = expr;
  std::stack<exprt> stactions;    // I'm not a continuation, honest guv'
  while (s.id() != ID_symbol)
  {
    if (s.id() == ID_index || s.id() == ID_member || s.id() == ID_dereference)
    {
      stactions.push(s);
      s = s.op0();
    }
    else
    {
      // Attempting to assign to something unreasonable
      // Your goto-program is broken
      std::ostringstream error_builder;
      error_builder << "unsupported assign ";
      error_builder << s.id();
      throw error_builder.str();
    }
  }

  const symbol_exprt &symbol_expr(to_symbol_expr(s));

  // This is the root abstract object that is in the map of abstract objects
  // It might not have the same type as value if the above stack isn't empty
  abstract_object_pointert final_value;

  if(!stactions.empty())
  {
    // The symbol is not in the map - it is therefore top
    abstract_object_pointert symbol_object;
    if(map.find(symbol_expr)==map.end())
    {
      symbol_object=abstract_object_factory(
        symbol_expr.type(), ns, true, false);
    }
    else
    {
      symbol_object=map[symbol_expr];
    }
    final_value=write(symbol_object, value, stactions, ns, false);
  }
  else
  {
    // We can assign the AO directly to the symbol
    final_value=value;
  }

  // Write the value for the root symbol back into the map
  assert(symbol_expr.type() == final_value->get_type());
  if (final_value->is_top())
  {
    map.erase(symbol_expr);
  }
  else
  {
    map[symbol_expr]=final_value;
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

  typedef std::function<
    abstract_object_pointert(
      abstract_object_pointert,  // The symbol we are modifying
      std::stack<exprt>, // The remaining stack
      abstract_object_pointert)> // The value we are writing.
      stacion_functiont;

  // Each handler takes the abstract object referenced, copies it,
  // writes according to the type of expression (e.g. for ID_member)
  // we would (should!) have an abstract_struct_objectt which has a
  // write_member which will attempt to update the abstract object for the
  // relevant member. This modified abstract object is returned and this
  // is inserted back into the map
  std::map<irep_idt, stacion_functiont> handlers=
  {
    {
      ID_index, [&](
        const abstract_object_pointert lhs_object,
        std::stack<exprt> stack,
        abstract_object_pointert rhs_object)
      {
        sharing_ptrt<array_abstract_objectt> array_abstract_object=
          std::dynamic_pointer_cast<array_abstract_objectt>(lhs_object);

        sharing_ptrt<array_abstract_objectt> modified_array=
          array_abstract_object->write_index(
            *this,
            stack,
            to_index_expr(next_expr),
            rhs_object,
            merge_write);

        return modified_array;
      }
    },
    {
      ID_member, [&](
        const abstract_object_pointert lhs_object,
        std::stack<exprt> stack,
        abstract_object_pointert rhs_object)
      {
        sharing_ptrt<struct_abstract_objectt> struct_abstract_object=
          std::dynamic_pointer_cast<struct_abstract_objectt>(lhs_object);

        sharing_ptrt<struct_abstract_objectt> modified_struct=
          struct_abstract_object->write_component(
            *this,
            stack,
            to_member_expr(next_expr),
            rhs_object,
            merge_write);

        return modified_struct;
      }
    },
    {
      ID_dereference, [&](
        const abstract_object_pointert lhs_object,
        std::stack<exprt> stack,
        abstract_object_pointert rhs_object)
      {
        sharing_ptrt<pointer_abstract_objectt> pointer_abstract_object=
          std::dynamic_pointer_cast<pointer_abstract_objectt>(lhs_object);

        sharing_ptrt<pointer_abstract_objectt> modified_pointer=
          pointer_abstract_object->write_dereference(
            *this, ns, stack, rhs_object, merge_write);

        return modified_pointer;
      }
    }
  };

  // We added something to the stack that we couldn't deal with
  assert(handlers.find(next_expr.id())!=handlers.end());
  return handlers[next_expr.id()](lhs, remaining_stack, rhs);
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

  if (possibly_constant.id()!=ID_nil)  // I.E. actually a value
  {
    assert(possibly_constant.type().id()==ID_bool); // Should be of the right type

    if (possibly_constant.is_false())
    {
      bool currently_bottom = get_is_bottom();
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
  return abstract_object_factory(type, top, bottom, empty_constant_expr, ns);
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
  return abstract_object_factory(type, false, false, e, ns);
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
  const namespacet &ns) const
{
  return variable_sensitivity_object_factoryt::instance().get_abstract_object(
    type, top, bottom, e, ns);
}

/*******************************************************************\

Function: abstract_environmentt::merge

  Inputs:
   env - the other environment

 Outputs: A Boolean, true when the merge has changed something

 Purpose: Computes the join between "this" and "b"

\*******************************************************************/

bool abstract_environmentt::merge(const abstract_environmentt &env)
{
  // Use the sharing_map's "iterative over all differences" functionality
  // This should give a significant performance boost
  // We can strip down to just the things that are in both

  // for each entry in the incoming environment we need to either add it
  // if it is new, or merge with the existing key if it is not present



  if(is_bottom)
  {
    *this=env;
    return !env.is_bottom;
  }
  else if(env.is_bottom)
  {
    return false;
  }
  else
  {
    bool modified=false;
    for(const auto &entry:env.map)
    {
      if(map.find(entry.first)!=map.end())
      {
        bool object_modified=false;
        abstract_object_pointert new_object=map[entry.first]->merge(
          entry.second, object_modified);

      modified|=object_modified;
        map[entry.first]=new_object;

      }

      if(map[entry.first]->is_top())
      {
        map.erase(entry.first);
        modified=true;
#ifdef DEBUG
      std::cout << "Removing " << entry.first.get_identifier() << std::endl;
#endif
      }
    }

    std::vector<map_keyt> to_remove;
    for(const auto &entry : map)
    {
      if(env.map.find(entry.first)==env.map.end())
      {
        to_remove.push_back(entry.first);
      }
    }
    for(const map_keyt &key_to_remove : to_remove)
    {
      map.erase(key_to_remove);
#ifdef DEBUG
    std::cout << "Removing " << key_to_remove.get_identifier() << std::endl;
#endif
      modified=true;
    }

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
  is_bottom=false;
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
  is_bottom=true;
}

/*******************************************************************\

Function: abstract_environmentt::get_is_bottom

  Inputs:

 Outputs:

 Purpose: Gets whether the domain is bottom

\*******************************************************************/

bool abstract_environmentt::get_is_bottom() const
{
  return map.empty() && is_bottom;
}

/*******************************************************************\

Function: abstract_environmentt::get_is_top

  Inputs:

 Outputs:

 Purpose: Gets whether the domain is top

\*******************************************************************/

bool abstract_environmentt::get_is_top() const
{
  return map.empty() && !is_bottom;
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
    out << "\n";
  }
  out << "}\n";
}

abstract_object_pointert abstract_environmentt::eval_expression(
  const exprt &e, const namespacet &ns) const
{
  // Delegate responsibility of resolving to a boolean abstract object
  // to the abstract object being compared against
  abstract_object_pointert lhs=eval(e.op0(), ns);
  return lhs->expression_transform(e, *this, ns);
}
