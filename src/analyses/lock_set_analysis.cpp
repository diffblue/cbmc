/*******************************************************************\

Module: Lockset Analysis

Author: Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#include <iostream>

#include <util/config.h>
#include <util/xml_expr.h>
#include <util/xml.h>

#include "lock_set_analysis.h"

/*******************************************************************
 Function: lock_set_domaint::transform

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_set_domaint::transform(locationt from_l,
				 locationt to_l, ai_baset &ai, 
				 const namespacet &ns)
{
  switch (from_l->type)
  {
  case FUNCTION_CALL:
  {
    const code_function_callt &code = to_code_function_call(from_l->code);

    const exprt &function = code.function();

    if (function.id() == ID_symbol)
    {
      const irep_idt& function_name = to_symbol_expr(function).get_identifier();

      if (function_name == config.ansi_c.lock_function)
      {
	// retrieve argument
        // ASSUMPTION: lock is in the first argument
	if (code.arguments().size() >= 1)
	{
	  exprt arg = code.arguments()[0];

#if 1 //remove invalid lock objects (NULL)
      //TODO: this can be better resolved by a thread-sensitive analysis
      //        see comment in which_threads_internal.cpp
	  object_mapt lock_objects;
	  get_value_set(from_l).get_value_set(
	    arg, lock_objects, ns, false);
	  clean_update(lock_objects,object_map);
#else
	  get_value_set(from_l).get_value_set(
	    arg, object_map, ns, false);
#endif
	} // if
      } // if
      else if (function_name == config.ansi_c.unlock_function)
      {
	exprt arg = code.arguments()[0];

	const object_mapt locks_held = object_map;

	object_map.clear();

	object_mapt lock_objects;

	get_value_set(from_l).get_value_set(
	  arg, lock_objects, ns, false);

	const value_sett::object_map_dt &lock_objects_dt = lock_objects.read();
	const value_sett::object_map_dt &locks_held_dt = locks_held.read();

	for (value_sett::object_map_dt::const_iterator a_it =
	       locks_held_dt.begin(); a_it != locks_held_dt.end(); a_it++)
	{
	  if (lock_objects_dt.find(a_it->first) == lock_objects_dt.end())
	    value_sett::insert(object_map, a_it->first, a_it->second);
	} // for
      } // if
    } // if symbol
  } // case switch
  default:
    break;
	
  } // switch
}

/*******************************************************************
 Function: lock_set_domaint::clean_update

 Inputs:

 Outputs:

 Purpose: remove invalid lock objects

 \*******************************************************************/

void lock_set_domaint::clean_update(const object_mapt &new_objects, 
			   object_mapt &lock_objects)
{
  const value_sett::object_map_dt &new_objects_dt = 
    new_objects.read();
  for (value_sett::object_map_dt::const_iterator 
	 a_it = new_objects_dt.begin(); 
       a_it !=new_objects_dt.end(); a_it++)
  {
    if (value_sett::object_numbering[a_it->first].id()!="NULL-object")
      value_sett::insert(lock_objects, a_it->first, a_it->second);
  } 
}

/*******************************************************************
 Function: lock_set_analysist::initialize

 Inputs:

 Outputs:

 Purpose: 1. run a value set analysis to track lock objects
 2. propagate the lock sets

 \*******************************************************************/

void lock_set_analysist::initialize(const goto_programt &goto_program,
			  const namespacet &ns)
{
  baset::initialize(goto_program, ns);

  forall_goto_program_instructions(i_it, goto_program)
    static_cast<lock_set_domaint &>(get_state(i_it))
       .value_set_analysis = &value_set_analysis;
}

/*******************************************************************\

Function: lock_set_analysist::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void lock_set_analysist::convert(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  xmlt &dest) const
{
  source_locationt previous_location;

  forall_goto_program_instructions(i_it, goto_program)
  {
    const source_locationt &location=i_it->source_location;
    
    if(location==previous_location) continue;

    if(location.is_nil() || location.get_file()==irep_idt())
      continue;

    xmlt &i=dest.new_element("instruction");
    i.new_element()=::xml(location);
    
    xmlt &var=i.new_element("locks-held");

    const value_sett::object_map_dt 
      &object_map=(*this)[i_it].object_map.read();

    for(value_sett::object_map_dt::const_iterator
          o_it=object_map.begin();
	o_it!=object_map.end();
	o_it++)
    {
      const exprt &o=value_sett::object_numbering[o_it->first];
        
      std::string result = from_expr(ns, "", o);

#if 0 //more detailed output
      if(o.id()==ID_invalid || o.id()==ID_unknown)
	result=from_expr(ns, "", o);
      else
      {
	result="<"+from_expr(ns, "", o)+", ";
        
	if(o_it->second.offset_is_set)
	  result+=integer2string(o_it->second.offset)+"";
	else
	  result+='*';

	if(o.type().is_nil())
	  result+=", ?";
	else
	  result+=", "+from_type(ns, "", o.type());

	result+='>';
      }
#endif
      std::stringstream ss;
        
      xmlt::escape(result, ss);
        
      var.new_element("lock-held").data=
	ss.str();
    }
  }
}


/*******************************************************************
 Function: lock_set_analysist::convert

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_set_analysist::convert(const namespacet &ns,
				 const goto_functionst &goto_functions,
				 xmlt &dest)
{
  dest = xmlt("lock_set_analysis");

  for (goto_functionst::function_mapt::const_iterator f_it =
	 goto_functions.function_map.begin();
       f_it != goto_functions.function_map.end(); f_it++)
  {
    xmlt &f = dest.new_element("function");
    f.new_element("identifier").data = id2string(f_it->first);
    convert(ns, f_it->second.body, f_it->first, f);
  }
}

/*******************************************************************
 Function: lock_set_analysist::convert

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_set_analysist::convert(const namespacet &ns, const goto_programt &goto_program,
				 xmlt &dest)
{
  dest = xmlt("lock_set_analysis");

  convert(ns, goto_program, "", dest.new_element("program"));
}
