/*******************************************************************\

Module: Global dependency analysis

Author: Daniel Poetzl

\*******************************************************************/

#include "simple_dependency_analysis.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// get ids of functions that could be used as threads
void simple_dependency_analysist::get_thread_functions(
  std::set<irep_idt> &funcs)
{
  forall_goto_functions(f_it, goto_functions)
  {
    typedef goto_functionst::goto_functiont goto_functiont;
    const goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    // check return type
    const code_typet &code_type=goto_function.type;
    const typet &return_type=code_type.return_type();

    if(return_type.id()!=ID_pointer)
      continue;

    const pointer_typet &pointer_type=to_pointer_type(return_type);
    assert(pointer_type.has_subtype());
    const typet &subtype=pointer_type.subtype();

    if(subtype.id()!=ID_empty)
      continue;

    // check parameter type
    typedef code_typet::parameterst parameterst;
    const parameterst parameters=code_type.parameters();

    if(parameters.size()!=1)
      continue;

    const typet &parameter_type=parameters[0].type();

    if(parameter_type.id()!=ID_pointer)
      continue;

    const pointer_typet &par_pointer_type=to_pointer_type(parameter_type);
    assert(par_pointer_type.has_subtype());
    const typet &par_subtype=par_pointer_type.subtype();

    if(par_subtype.id()!=ID_empty)
      continue;

    funcs.insert(f_it->first);
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_dependency_analysist::get_returns(
  const goto_programt &goto_program,
  expr_vect &expr_vec,
  location_sett &location_set)
{
  assert(false);

  forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_return())
      continue;

    const code_returnt &code_return=to_code_return(i_it->code);

    if(!code_return.has_return_value())
      continue;

    expr_vec.push_back(code_return.return_value());
    location_set.insert(i_it);
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simple_dependency_analysist::handle_thread_create(
  locationt l,
  const argumentst &args,
  location_sett &other_locations,
  id_sett &id_set)
{
  bool changed=false;

  unsigned thread_no=config.ansi_c.create_thread_arg_no_of_function;
  assert(thread_no<args.size());
  exprt thread=args[thread_no];

  unsigned arg_no=config.ansi_c.create_thread_arg_no_of_arg;
  argumentst arguments;
  assert(arg_no<args.size());
  arguments.push_back(args[arg_no]);
  assert(arguments.size()==1);

  exprt lhs;
  lhs.make_nil();

  // check if thread is specified via function id
  if(thread.id()==ID_typecast || thread.id()==ID_address_of)
    thread=thread.op0();

  if(thread.id()==ID_symbol)
  {
    irep_idt id=misc::get_identifier(thread);
    assert(!id.empty());

    if(goto_functions.function_map.find(id)
       !=goto_functions.function_map.end())
    {
      if(handle_function_call(id, l, lhs, arguments, other_locations, id_set))
        changed=true;

      return changed;
    }
  }

  // do for all functions that might be threads
  std::set<irep_idt> thread_functions;
  get_thread_functions(thread_functions);

  for(std::set<irep_idt>::const_iterator it=thread_functions.begin();
      it!=thread_functions.end(); it++)
  {
    irep_idt id=*it;
    assert(!id.empty());

    if(handle_function_call(id, l, lhs, arguments, other_locations, id_set))
      changed=true;
  }

  return changed;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simple_dependency_analysist::is_handled(irep_idt id)
{
  std::string s=id2string(id);

  if(s==config.ansi_c.lock_function ||
     s==config.ansi_c.unlock_function ||
     s==config.ansi_c.create_thread ||
     s==config.ansi_c.join_thread)
    return true;

  return false;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simple_dependency_analysist::handle_function_call(
  irep_idt id, // called function
  locationt l,
  const exprt &lhs, // target of assignment of return value
  const argumentst &args, // args to function call
  location_sett &other_locations,
  id_sett &id_set) // symbols collected so far
{
  bool changed=false;

  // result set for symbols of an expression
  std::unique_ptr<gather_symbolst> gsp1(create_gather_symbols());
  gather_symbolst &gather_symbols1=*gsp1;

  goto_functionst::function_mapt::const_iterator cf_it
    =goto_functions.function_map.find(id);
  if(cf_it==goto_functions.function_map.end())
    return false;

  const goto_functiont &goto_function=cf_it->second;
  if(!goto_function.body_available())
  {
    if(!is_handled(id))
      return false;

    assert(gather_symbols1.empty());
    lhs.visit(gather_symbols1);
    for(argumentst::const_iterator it=args.begin();
        it!=args.end(); it++)
    {
      it->visit(gather_symbols1);
    }
    if(have_common_elements(gather_symbols1, id_set))
    {
      unsigned n=id_set.size();
      id_set.insert(gather_symbols1.begin(), gather_symbols1.end());
      if(id_set.size()!=n)
        changed=true;
    }
    return changed;
  }

  assert(goto_function.body_available());

  // get parameters of called function
  std::vector<irep_idt> pars=goto_function.type.parameter_identifiers();

  assert(lhs.id()==ID_nil); // use remove_returns

#if 0
  // first handle function return
  if(lhs.id()!=ID_nil)
  {
    expr_vect expr_vec;
    location_sett location_set;
    get_returns(goto_function.body, expr_vec, location_set);

    gather_symbols_ao.clear();

    for(expr_vect::const_iterator it=expr_vec.begin();
        it!=expr_vec.end(); it++)
    {
      it->visit(gather_symbols_ao);
    }

    gather_symbols_all.clear();
    lhs.visit(gather_symbols_all);

    if(have_common_elements(gather_symbols_all, id_set) ||
       have_common_elements(gather_symbols_ao, id_set))
    {
      other_locations.insert(location_set.begin(), location_set.end());

      unsigned n=id_set.size();
      id_set.insert(gather_symbols_all.begin(), gather_symbols_all.end());
      id_set.insert(gather_symbols_ao.begin(), gather_symbols_ao.end());
      if(id_set.size()!=n)
        changed=true;
    }
  }
#endif

  // ignore vararg functions
  const code_typet &code_type=goto_function.type;
  if(code_type.has_ellipsis())
    return changed;

  if(args.size()!=pars.size())
    return changed;

  assert(args.size()==pars.size());

  // handle all arguments
  unsigned n=args.size();
  for(unsigned i=0; i<n; i++)
  {
    const exprt &expr=args[i];
    gather_symbols1.clear();
    expr.visit(gather_symbols1);

    irep_idt par=pars[i];

    if(have_common_elements(gather_symbols1, id_set) ||
       id_set.find(par)!=id_set.end())
    {
      unsigned n=id_set.size();
      id_set.insert(gather_symbols1.begin(), gather_symbols1.end());
      id_set.insert(par);
      if(id_set.size()!=n)
        changed=true;
    }
  }

  return changed;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_dependency_analysist::postprocess(
  location_sett &location_set,
  const id_sett &id_set)
{
  // gather functions that have a dependent location
  std::set<irep_idt> funcs;
  for(location_sett::const_iterator it=location_set.begin();
      it!=location_set.end(); it++)
  {
    irep_idt id=(*it)->function;
    assert(!id.empty());
    funcs.insert(id);
  }

  bool changed;

  // gather significant calls
  do
  {
    changed=false;

    forall_goto_functions(f_it, goto_functions)
    {
      const goto_functiont &goto_function=f_it->second;

      if(!goto_function.body_available()) // no locations
        continue;

      const goto_programt &goto_program=goto_function.body;

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(i_it->is_function_call())
        {
          // get name of called function
          irep_idt id=misc::get_function_name(i_it);

          if(id.empty())
            continue;

          std::string s=id2string(id); // called function

          // lock functions must be in the location set already
          assert((s!=config.ansi_c.lock_function &&
                 s!=config.ansi_c.unlock_function) ||
                 location_set.find(i_it)!=location_set.end());

          // thread create must be in the location set already
          assert(s!=config.ansi_c.create_thread ||
                 location_set.find(i_it)!=location_set.end());

          // only functions with body can be significant
          if(funcs.find(id)!=funcs.end())
          {
            location_set.insert(i_it);

            unsigned n=funcs.size();
            funcs.insert(i_it->function); // function of call
            if(funcs.size()!=n)
              changed=true;
          }
        }
      }
    }
  } while(changed);

  // gather the rest from dependent functions
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;

    if(funcs.find(f_it->first)==funcs.end())
      continue; // not a significant function

    if(!goto_function.body_available())
      continue; // no locations

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_function_call())
      {
        // get name of called function
        irep_idt id=misc::get_function_name(i_it);

        if(id.empty())
          continue;

        goto_functionst::function_mapt::const_iterator it
          =goto_functions.function_map.find(id);

        if(it==goto_functions.function_map.end() ||
           !it->second.body_available())
        {
          location_set.insert(i_it);
        }
      }
      else if(!i_it->is_assign())
      {
        assert(!i_it->is_function_call());
        location_set.insert(i_it);
      }
    }
  }

  // compute stats
  assert(num_assignments==0);
  assert(num_significant_assignments==0);

  assert(num_functions==0);
  assert(num_functions_body==0);
  assert(num_significant_functions_body==0);

  num_functions=goto_functions.function_map.size();

  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    num_functions_body++;

    if(funcs.find(f_it->first)!=funcs.end())
      num_significant_functions_body++;

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_assign())
      {
        num_assignments++;
        if(location_set.find(i_it)!=location_set.end())
          num_significant_assignments++;
      }
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_dependency_analysist::operator()(
  const expr_vect &expr_vec,
  location_sett &location_set,
  id_sett &id_set)
{
  assert(!expr_vec.empty());
  assert(location_set.empty());
  assert(id_set.empty());

  // result set for symbols of an expression
  std::unique_ptr<gather_symbolst> gsp1(create_gather_symbols());
  gather_symbolst &gather_symbols1=*gsp1;

  std::unique_ptr<gather_symbolst> gsp2(create_gather_symbols());
  gather_symbolst &gather_symbols2=*gsp2;

  // gather all symbols from starting expressions
  for(expr_vect::const_iterator it=expr_vec.begin();
      it!=expr_vec.end(); it++)
  {
    gather_symbols1.clear();
    it->visit(gather_symbols1);
    id_set.insert(gather_symbols1.begin(), gather_symbols1.end());
  }

  if(id_set.empty())
    return;

  location_sett other_locations;

  num_iterations=0;

  bool changed;

  // do fixedpoint
  do
  {
    changed=false;

    num_iterations++;

    forall_goto_functions(f_it, goto_functions)
    {
      const goto_functiont &goto_function=f_it->second;

      if(!goto_function.body_available())
        continue;

      const goto_programt &goto_program=goto_function.body;

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(i_it->is_assign())
        {
#if 0
          // optimization
          if(location_set.find(i_it)!=location_set.end())
            continue;
#endif

          // gather all symbols in the assignment
          const code_assignt &code=to_code_assign(i_it->code);
          const exprt &lhs=code.lhs();
          const exprt &rhs=code.rhs();

          gather_symbols1.clear();
          lhs.visit(gather_symbols1);
          gather_symbols2.clear();
          rhs.visit(gather_symbols2);

          if(have_common_elements(gather_symbols1, id_set) ||
             have_common_elements(gather_symbols2, id_set))
          {
            location_set.insert(i_it);

            // update symbol set
            gather_symbols1.clear();
            code.visit(gather_symbols1);

            unsigned n=id_set.size();
            id_set.insert(gather_symbols1.begin(), gather_symbols1.end());
            if(id_set.size()!=n)
              changed=true;
          }
        }
        else if(i_it->is_function_call())
        {
#if 0
          location_set.insert(i_it);
#endif

          // get name of called function
          irep_idt id=misc::get_function_name(i_it);

          if(id.empty())
            continue;

          // get function call arguments
          code_function_callt code=to_code_function_call(i_it->code);
          argumentst args=code.arguments();

          std::string s=id2string(id);

          // special handling for pthread_create
          if(s==config.ansi_c.create_thread)
          {
            location_set.insert(i_it);

            if(handle_thread_create(
                i_it, // call location
                args,
                other_locations,
                id_set))
              changed=true;
          }
          else if(s==config.ansi_c.lock_function ||
                  s==config.ansi_c.unlock_function)
          {
            location_set.insert(i_it);
          }
          else
          {
            // target of assignment
            const exprt &lhs=code.lhs();

            if(handle_function_call(
                id, // called function
                i_it, // call location
                lhs, // target of assignment of return value
                args, // args to function call
                other_locations,
                id_set))
              changed=true;
          }
        }
        else
        {
#if 0
          location_set.insert(i_it);
#endif
        }
      } // for all goto instructions
    } // for all goto functions
  } while(changed);

  // merge calls into location set
  location_set.insert(other_locations.begin(), other_locations.end());

  postprocess(location_set, id_set);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_dependency_analysist::output_stats(std::ostream &out) const
{
  out << "*** Statistics: " << "\n";
  out << "  Number of assignments: " << num_assignments << "\n";
  out << "  Number of significant assignments: " << num_significant_assignments
    << "\n";
  out << "  Number of functions: " << num_functions << "\n";
  out << "  Number of functions with body: " << num_functions_body << "\n";
  out << "  Number of significant functions with body: " <<
    num_significant_functions_body << "\n";
  out << "  Number of fixpoint iterations: " << num_iterations;
}
