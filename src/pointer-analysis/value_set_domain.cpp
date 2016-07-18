/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/prefix.h>
#include <util/std_code.h>

#include "value_set_domain.h"


/*******************************************************************\

Function: value_set_domaint::merge_shared

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_domaint::merge_shared(
  const value_set_domaint &other,
  locationt from,
  locationt to,
  const namespacet &ns)
{
  if(value_set.is_bottom && other.value_set.is_bottom)
    return false;

  bool changed = value_set.is_bottom && !other.value_set.is_bottom;

    // TODO: dirty vars
#if 0
  reaching_definitions_analysist *rd=
    dynamic_cast<reaching_definitions_analysist*>(&ai);
  assert(rd!=0);
#endif

  hash_set_cont<irep_idt, irep_id_hash> selected_vars;

  for(value_sett::valuest::const_iterator ito=other.value_set.values.begin();
      ito!=other.value_set.values.end();
      ++ito)
  {
    const irep_idt &identifier=ito->first;

    #ifdef DEBUG
      std::cout << "Symbol " << identifier << std::endl;
    #endif

    if(has_prefix(id2string(identifier), "value_set::"))
      continue;

    if(!is_shared(identifier, ns) /*&&
       !rd.get_is_dirty()(identifier)*/)
      continue;
    
    selected_vars.insert(identifier);

    #ifdef DEBUG
      std::cout << "   SHARED " << std::endl;
    #endif

  }

  value_set.is_bottom = false;
  return value_set.make_union(other.value_set.values, selected_vars) 
    || changed;
}

/*******************************************************************\

Function: value_set_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_domaint::transform_internal(
  locationt from_l,
  locationt to_l,
  unsigned don, // dynamic object number
  ai_baset &ai,
  const namespacet &ns)
{
  switch(from_l->type)
  {
  case GOTO:
    // ignore for now
    break;

  case END_FUNCTION:    
    value_set.do_end_function(get_return_lhs(to_l), ns, don);
    value_set.remove_parameters(from_l->function, ns);
    break;
  
  case RETURN:
  case OTHER:
  case ASSIGN:
  case DECL:
    value_set.apply_code(from_l->code, ns, don);
    break;
    
  case ASSUME:
    value_set.guard(from_l->guard, ns, don);
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code=
        to_code_function_call(from_l->code);
      const exprt &function=code.function();

      if(function.id()==ID_symbol)
      {
        const irep_idt &identifier=function.get(ID_identifier);
        assert(!identifier.empty());

        if (id2string(identifier)==config.ansi_c.create_thread &&
            id2string(to_l->function)!=config.ansi_c.create_thread)
        {
          typedef code_function_callt::argumentst argumentst;
          const argumentst &arguments=code.arguments();
          assert(arguments.size()>config.ansi_c.create_thread_arg_no_of_arg);
          unsigned arg_idx=config.ansi_c.create_thread_arg_no_of_arg;

          argumentst new_arguments;
          new_arguments.push_back(arguments[arg_idx]);
          value_set.do_function_call(to_l->function, new_arguments, ns, don);

          break;
        }
      }

      value_set.do_function_call(to_l->function, code.arguments(), ns, don);
    }
    break;

  case DEAD:
    {
      const code_deadt &code=
         to_code_dead(from_l->code);
      value_set.values.erase(code.get_identifier());
    }
    break;
  
  default:;
    // do nothing
  }
}

/*******************************************************************\

Function: value_set_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_domaint::transform(
  locationt from_l,
  locationt to_l,
  ai_baset &ai,
  const namespacet &ns)
{
  unsigned dynamic_object_number=from_l->location_number;
  transform_internal(from_l, to_l, dynamic_object_number, ai, ns);
}

/*******************************************************************\

Function: value_set_domaint::is_shared

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_domaint::is_shared(
  const irep_idt &identifier,
  const namespacet &ns)
{
  std::string id=id2string(identifier);

  // get identifier of root object: struct
  std::size_t pos_dot=id.find('.');
  id=id.substr(0,pos_dot);

  std::size_t pos_bracket=id.find('[');
  id=id.substr(0,pos_bracket);

  const symbolt &symbol=ns.lookup(id);

  bool result=symbol.is_shared();

  return result;
}

/*******************************************************************\

Function: value_set_domaint::get_return_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt value_set_domaint::get_return_lhs(locationt to)
{
  // get predecessor of "to"

  to--;

  if(to->is_end_function())
    return static_cast<const exprt &>(get_nil_irep());
  
  // must be the function call
  assert(to->is_function_call());

  const code_function_callt &code=
    to_code_function_call(to->code);
  
  return code.lhs();
}

