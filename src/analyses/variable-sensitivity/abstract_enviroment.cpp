/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include "abstract_enviroment.h"
#include <functional>
#include <stack>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/ai.h>



/*******************************************************************\

Function: abstract_environmentt::eval

  Inputs:
   expr - the expression to evaluate

 Outputs: The abstract_object representing the value of the expression

 Purpose: Evaluate the value of an expression

\*******************************************************************/

abstract_object_pointert abstract_environmentt::eval(
  const exprt &expr) const
{
  typedef std::function<abstract_object_pointert(const exprt &)> eval_handlert;
  static std::map<irep_idt, eval_handlert> handlers=
  {
    {
      ID_symbol, [&](const exprt &expr)
      {
        const symbol_exprt &symbol(to_symbol_expr(expr));
        const auto &symbol_entry=map.find(symbol);
        if(symbol_entry==map.cend())
        {
          return abstract_object_factory(expr.type(), true);
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
          expr.type(), to_constant_expr(expr));
      }
    },
    {
      ID_member, [&](const exprt &expr)
      {
#if 0
        member_exprt member_expr(to_member_expr(expr));
#endif
        // TODO(tkiley): eval the compound to (hopefully) get an
        // abstract_struct_objectt then use that to get an AO for a specific
        // component.
        // For now, just return top
        return abstract_object_pointert(
          new abstract_objectt(expr.type(), true, false));
      }
    },
    {
      ID_address_of, [&](const exprt &expr)
      {
#if 0
        address_of_exprt address_expr(to_address_of_expr(expr));
#endif
        // TODO(tkiley): This needs special handling
        // For now just return top
        return abstract_object_pointert(
          new abstract_objectt(expr.type(), true, false));
      }
    },
    {
      ID_dereference, [&](const exprt &expr)
      {
  #if 0
        dereference_exprt dereference(to_dereference_expr(expr));
  #endif
        // TODO(tkiley): eval the pointer to (hopefully) get an
        // abstract_pointer_objectt then use that to get an AO for a specific
        // value.
        // For now, just return top
        return abstract_object_pointert(
          new abstract_objectt(expr.type(), true, false));
      }
    },
    {
      ID_index, [&](const exprt &expr)
      {
#if 0
        index_exprt index_expr(to_index_expr(expr));
#endif
        // TODO(tkiley): eval the array to (hopefully) get an
        // abstract_array_objectt then use that to get an AO for a specific
        // index.
        // For now, just return top
        return abstract_object_pointert(
          new abstract_objectt(expr.type(), true, false));
      }
    }
  };
  #if 0
  [&](const exprt &expr)
        {
          return abstract_object_factory(
            expr.type(), to_constant_expr(expr));
        }
      }
#endif
  const auto &handler=handlers.find(expr.id());
  if(handler==handlers.cend())
  {
    return abstract_object_factory(expr.type(), true);
  }
  else
  {
    return handler->second(expr);
  }
}

/*******************************************************************\

Function: abstract_environmentt::assign

  Inputs:
   expr - the expression to assign to
   value - the value to assign to the expression

 Outputs: ?

 Purpose: Assign a value to an expression

\*******************************************************************/

bool abstract_environmentt::assign(
  const exprt &expr, const abstract_object_pointert value)
{
  exprt s = expr;
  std::stack<exprt> stactions;    // I'm not a continuation, honest guv'

  while (s.id() != ID_symbol)
  {
    if (s.id() == ID_index || s.id() == ID_member)
    {
      stactions.push(s);
      s = s.op0();
    }
    else if (s.id() == ID_dereference)
    {
      // LOL, nope!
    }
    else
    {
      // Attempting to assign to something unreasonable
      // Your goto-program is broken
      throw "die_horribly";
    }
  }

  const symbol_exprt &symbol_expr(to_symbol_expr(s));

  if (!stactions.empty())
  {
    throw "not yet implemented";
  }
  if (value->is_top())
  {
    map.erase(symbol_expr);
  }
  else
  {
    map[symbol_expr]=value;
  }

  return true;
}

/*******************************************************************\

Function: abstract_environmentt::assume

  Inputs:
   expr - the expression inside the assume

 Outputs: ?

 Purpose: ?

\*******************************************************************/

bool abstract_environmentt::assume(const exprt &expr)
{
  abstract_object_pointert res = eval(expr);
  std::string not_implemented_string=__func__;
  not_implemented_string.append(" not implemented");
  throw not_implemented_string;
  // Need abstract_booleant
#if 0
  abstract_booleant *b = dynamic_cast<abstract_booleant>(res);

  assert(b != NULL);

  if (b->to_constant().is_false())
  {
    make_bottom();
    return true;
  }
  else
    return false;
#endif
}


/*******************************************************************\

Function: abstract_environmentt::abstract_object_factory

  Inputs:
   type - the type of the object whose state should be tracked
   top - does the type of the object start as top

 Outputs: The abstract object that has been created

 Purpose: Look at the configuration for the sensitivity and create an
          appropriate abstract_object

\*******************************************************************/

abstract_object_pointert abstract_environmentt::abstract_object_factory(
  const typet type, bool top) const
{
  // TODO (tkiley): Here we should look at some config file
  if(type.id()==ID_signedbv)
  {
    return abstract_object_pointert(
      new constant_abstract_valuet(type, top, false));
  }
  else
  {
    return abstract_object_pointert(new abstract_objectt(type, top, false));
  }
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
  const typet type, const constant_exprt e) const
{
  assert(type==e.type());
  if(type.id()==ID_signedbv)
  {
    return abstract_object_pointert(
      new constant_abstract_valuet(e));
  }
  else
  {
    return abstract_object_pointert(new abstract_objectt(e));
  }
}

/*******************************************************************\

Function: abstract_environmentt::merge

  Inputs:
   env - the other environment

 Outputs: ?

 Purpose: ?

\*******************************************************************/

bool abstract_environmentt::merge(const abstract_environmentt &env)
{
  // Use the sharing_map's "iterative over all differences" functionality
  // This should give a significant performance boost
  // We can strip down to just the things that are in both

  // for each entry in the incoming environment we need to either add it
  // if it is new, or merge with the existing key if it is not present

  bool modified=false;
  for(const auto &entry:env.map)
  {
    if(map.find(entry.first)==map.end())
    {
      // We only add new stuff if we are bottom
      if(is_bottom)
      {
        map[entry.first] = entry.second;
        modified=true;
      }
    }
    else
    {
      bool object_modified=false;
      abstract_object_pointert new_object=map[entry.first]->merge(
        entry.second, object_modified);

      if(object_modified)
      {
        modified=true;
      }
      map[entry.first]=new_object;

    }

    if(map[entry.first]->is_top())
    {
      map.erase(entry.first);
      is_bottom=false;
      modified=true;
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
  }
  return modified;
}

/*******************************************************************\

Function: abstract_environmentt::havoc

  Inputs:
   havoc_string - debug string to track down havoc causing.

 Outputs:

 Purpose: Set the domain to top

\*******************************************************************/

void abstract_environmentt::havoc(const std::string &havoc_string)
{
  // TODO(tkiley): error reporting
  make_top();
}

/*******************************************************************\

Function: abstract_environmentt::make_top

  Inputs:

 Outputs:

 Purpose: Set the domain to top

\*******************************************************************/

void abstract_environmentt::make_top()
{
  // since we assume anything is not in the map is top this is sufficient
  // TODO: need a flag for bottom
  map.clear();
  is_bottom=false;
}

/*******************************************************************\

Function: abstract_environmentt::make_bottom

  Inputs:

 Outputs:

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
   ai - ?
   ns - ?

 Outputs:

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

abstract_object_pointert abstract_environmentt::eval_logical(
  const exprt &e) const
{
  throw "not implemented";
}

abstract_object_pointert abstract_environmentt::eval_rest(const exprt &e) const
{
  return abstract_object_factory(e.type());
}
