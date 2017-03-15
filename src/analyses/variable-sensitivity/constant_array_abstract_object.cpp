/*******************************************************************\

 Module: Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "constant_array_abstract_object.h"

constant_array_abstract_objectt::constant_array_abstract_objectt(typet type):
array_abstract_objectt(type)
{}

constant_array_abstract_objectt::constant_array_abstract_objectt(
  typet type, bool top, bool bottom):
array_abstract_objectt(type, top, bottom)
{}

constant_array_abstract_objectt::constant_array_abstract_objectt(
  const constant_array_abstract_objectt &old):
    array_abstract_objectt(old)
{
  for(const auto &entry : old.map)
  {
    map[entry.first]=abstract_object_pointert(entry.second->clone());
  }
}

constant_array_abstract_objectt::constant_array_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns):
    array_abstract_objectt(expr, environment, ns)
{
  if(expr.id()==ID_array)
  {
    int index=0;
    for(const exprt &entry : expr.operands())
    {
      map[mp_integer(index)]=environment.eval(entry, ns);
      ++index;
    }
    top=false;
  }
}

void constant_array_abstract_objectt::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  if(is_top() || is_bottom())
  {
    array_abstract_objectt::output(out, ai, ns);
  }
  else
  {
    out << "{";
    for(const auto &entry : map)
    {
      out << "[" << entry.first << "] = ";
      entry.second->output(out, ai, ns);
      out << "\n";
    }
    out << "}";
  }
}

abstract_object_pointert constant_array_abstract_objectt::read_index(
  const abstract_environmentt &env,
  const index_exprt &index,
  const namespacet &ns) const
{
  mp_integer index_value;
  if(eval_index(index, env, ns, index_value))
  {
    // Here we are assuming it is always in bounds
    if(map.find(index_value)==map.cend())
    {
      return env.abstract_object_factory(type().subtype(), ns, true, false);
    }
    else
    {
      return map.find(index_value)->second;
    }
  }
  else
  {
    // Reading from somewhere in the array
    // TODO(tkiley): merge all the values of the array, we may be able to
    // do better than returning top
    return env.abstract_object_factory(type().subtype(), ns, true, false);
  }
}

sharing_ptrt<array_abstract_objectt>
  constant_array_abstract_objectt::write_index(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const index_exprt &index_expr,
    const abstract_object_pointert value,
    bool merging_write) const
{
  if(is_bottom())
  {
    return array_abstract_objectt::write_index(
      environment, ns, stack, index_expr, value, merging_write);
  }
  else
  {
    if(stack.empty())
    {
      auto copy=
        internal_sharing_ptrt<constant_array_abstract_objectt>(
          new constant_array_abstract_objectt(*this));

      mp_integer index_value;
      if(!merging_write && eval_index(index_expr, environment, ns, index_value))
      {
        if(is_top())
        {
          copy->top=false;
        }

        copy->map[index_value]=value;
        return copy;
      }
      else
      {
        // try to write to all
        // TODO(tkiley): Merge with each entry
        return array_abstract_objectt::write_index(
          environment, ns, stack, index_expr, value, merging_write);
      }
    }
    else
    {
      auto copy=
        internal_sharing_ptrt<constant_array_abstract_objectt>(
          new constant_array_abstract_objectt(*this));

      mp_integer index_value;
      if(eval_index(index_expr, environment, ns, index_value))
      {
        // Here we assume the write is in bounds
        abstract_object_pointert array_entry;
        if(map.find(index_value)==map.cend())
        {
          array_entry=map.at(index_value);
        }
        else
        {
          array_entry=get_top_entry(environment, ns);
        }

        if(is_top())
        {
          copy->top=false;
        }
        copy->map[index_value]=environment.write(
          array_entry, value, stack, ns, merging_write);

        return copy;
      }
      else
      {
        for(const auto &array_entry : map)
        {
          // Merging write since we don't know which index we are writing to
          copy->map[array_entry.first]=
            environment.write(
              array_entry.second, value, stack, ns, true);
          if(is_top())
          {
            copy->top=false;
          }
        }

        return copy;
      }
    }
  }
}

// Purpose: Short hand method for creating a top element of the array
abstract_object_pointert constant_array_abstract_objectt::get_top_entry(
  const abstract_environmentt &env, const namespacet &ns) const
{
  return env.abstract_object_factory(type().subtype(), ns, true, false);
}

bool constant_array_abstract_objectt::eval_index(
  const index_exprt &index,
  const abstract_environmentt &env,
  const namespacet &ns,
  mp_integer &out_index) const
{
  abstract_object_pointert index_abstract_object=env.eval(index.index(), ns);
  exprt value=index_abstract_object->to_constant();
  if(value.is_constant())
  {
    constant_exprt constant_index=to_constant_expr(value);
    out_index=binary2integer(id2string(constant_index.get_value()), false);
    return true;
  }
  else
  {
    return false;
  }
}
