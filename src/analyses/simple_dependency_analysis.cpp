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

  // gather significant calls
  bool changed;
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

          assert(!is_handled(id) ||
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
  std::unique_ptr<gather_symbolst> gsp(create_gather_symbols());
  gather_symbolst &gather_symbols=*gsp;

  // gather all symbols from starting expressions
  for(expr_vect::const_iterator it=expr_vec.begin();
      it!=expr_vec.end(); it++)
  {
    it->visit(gather_symbols);
  }

  gather_ids(gather_symbols, id_set);

  // gather significant statements
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
        const code_assignt &code=to_code_assign(i_it->code);
        gather_symbols.clear();
        code.visit(gather_symbols);

        if(have_common_elements(gather_symbols, id_set))
        {
          location_set.insert(i_it);
        }
      }
      else if(i_it->is_function_call())
      {
        // get name of called function
        irep_idt id=misc::get_function_name(i_it);

        if(id.empty())
          continue;

        if(is_handled(id))
          location_set.insert(i_it);
      }
    }
  }

  postprocess(location_set, id_set);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_dependency_analysist::handle_call(
  irep_idt id,
  argumentst &args,
  std::vector<id_sett> &id_set_vec)
{
  goto_functionst::function_mapt::const_iterator cf_it
    =goto_functions.function_map.find(id);
  if(cf_it==goto_functions.function_map.end())
    return;

  const goto_functiont &goto_function=cf_it->second;

  if(!goto_function.body_available())
    return;

  // get parameters of called function
  std::vector<irep_idt> pars=goto_function.type.parameter_identifiers();

  // ignore vararg functions
  const code_typet &code_type=goto_function.type;
  if(code_type.has_ellipsis())
    return;

  if(args.size()!=pars.size())
    return;

  assert(args.size()==pars.size());

  std::unique_ptr<gather_symbolst> gsp(create_gather_symbols());
  gather_symbolst &gather_symbols=*gsp;

  // handle all arguments
  unsigned n=args.size();
  for(unsigned i=0; i<n; i++)
  {
    const exprt &expr=args[i];
    gather_symbols.clear();
    expr.visit(gather_symbols);

    irep_idt par=pars[i];
    gather_symbols.insert(par);

    id_set_vec.push_back(gather_symbols);
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_dependency_analysist::gather_ids(
  const id_sett &start_id_set,
  id_sett &global_id_set)
{
  assert(global_id_set.empty());

  std::vector<id_sett> id_set_vec;
  std::map<irep_idt, std::set<unsigned>> symbol_map;

  std::unique_ptr<gather_symbolst> gsp(create_gather_symbols());
  gather_symbolst &gather_symbols=*gsp;

  // First phase: gather symbol sets for assignments/calls

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
        const code_assignt &code=to_code_assign(i_it->code);
        gather_symbols.clear();
        code.visit(gather_symbols);

        id_set_vec.push_back(gather_symbols);
      }
      else if(i_it->is_function_call())
      {
        // get name of called function
        irep_idt id=misc::get_function_name(i_it);

        if(id.empty())
          continue;

        std::string s=id2string(id);

        // get function call arguments
        code_function_callt code=to_code_function_call(i_it->code);
        argumentst args=code.arguments();

        // special handling for pthread_create
        if(s==config.ansi_c.create_thread)
        {
          unsigned thread_no=config.ansi_c.create_thread_arg_no_of_function;
          assert(thread_no<args.size());
          exprt thread=args[thread_no];

          unsigned arg_no=config.ansi_c.create_thread_arg_no_of_arg;
          argumentst arguments;
          assert(arg_no<args.size());
          arguments.push_back(args[arg_no]);
          assert(arguments.size()==1);

          bool handled=false;

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
              handle_call(id, arguments, id_set_vec);
              handled=true;
            }
          }

          if(!handled)
          {
            // do for all functions that might be threads
            std::set<irep_idt> thread_functions;
            get_thread_functions(thread_functions);

            for(std::set<irep_idt>::const_iterator it=thread_functions.begin();
                it!=thread_functions.end(); it++)
            {
              irep_idt id=*it;
              assert(!id.empty());
              handle_call(id, arguments, id_set_vec);
            }
          }
        }
        else
        {
          handle_call(id, args, id_set_vec);
        }
      }
    }
  }

#if 0
  std::cout << "====================" << std::endl;
  std::cout << "First phase results:" << std::endl;
  std::cout << "====================" << std::endl;

  for(std::vector<id_sett>::const_iterator it=id_set_vec.begin();
      it!=id_set_vec.end(); it++)
  {
    const id_sett &id_set=*it;
    unsigned idx=std::distance(id_set_vec.cbegin(), it);
    std::cout << "Item: " << idx << std::endl;

    for(id_sett::const_iterator id_it=id_set.begin();
        id_it!=id_set.end(); id_it++)
    {
      std::cout << *id_it << std::endl;
    }
  }
#endif

  // Second phase: build symbol map

  for(std::vector<id_sett>::const_iterator it=id_set_vec.begin();
      it!=id_set_vec.end(); it++)
  {
    const id_sett &id_set=*it;
    unsigned idx=std::distance(id_set_vec.cbegin(), it);

    for(id_sett::const_iterator id_it=id_set.begin();
        id_it!=id_set.end(); id_it++)
    {
      irep_idt id=*id_it;
      symbol_map[id].insert(idx);
    }
  }

#if 0
  std::cout << "=====================" << std::endl;
  std::cout << "Second phase results:" << std::endl;
  std::cout << "=====================" << std::endl;

  for(std::map<irep_idt, std::set<unsigned>>::const_iterator it
      =symbol_map.begin(); it!=symbol_map.end(); it++)
  {
    irep_idt id=it->first;
    std::cout << "Symbol: " << id << std::endl;

    const std::set<unsigned> &idx_set=it->second;

    for(std::set<unsigned>::const_iterator idx_it=idx_set.begin();
        idx_it!=idx_set.end(); idx_it++)
    {
      unsigned idx=*idx_it;
      id_sett &id_set=id_set_vec[idx];

      std::cout << "Symbol set:" << std::endl;
      for(id_sett::const_iterator id_it=id_set.begin();
          id_it!=id_set.end(); id_it++)
      {
        irep_idt id=*id_it;
        std::cout << id << std::endl;
      }
    }
  }
#endif

  // Third phase: compute transitive dependencies

  id_sett symbols_next;
  symbols_next.insert(start_id_set.begin(), start_id_set.end());

  id_sett symbols_handled;

  global_id_set.insert(start_id_set.begin(), start_id_set.end());

  while(!symbols_next.empty())
  {
    id_sett::const_iterator id_it=symbols_next.begin();
    irep_idt id=*id_it;
    symbols_next.erase(id_it);

    const std::set<unsigned> &idx_set=symbol_map[id];

    for(std::set<unsigned>::const_iterator it=idx_set.begin();
        it!=idx_set.end(); it++)
    {
      unsigned idx=*it;
      const id_sett &id_set=id_set_vec[idx];

      global_id_set.insert(id_set.begin(), id_set.end());

      for(id_sett::const_iterator id_it=id_set.begin();
          id_it!=id_set.end(); id_it++)
      {
        irep_idt id=*id_it;
        if(symbols_handled.find(id)==symbols_handled.end())
        {
          symbols_handled.insert(id);
          symbols_next.insert(id);
        }
      }
    }
  }

#if 0
  std::cout << "====================" << std::endl;
  std::cout << "Third phase results:" << std::endl;
  std::cout << "====================" << std::endl;

  for(id_sett::const_iterator it=global_id_set.begin();
      it!=global_id_set.end(); it++)
  {
    std::cout << *it << std::endl;
  }
#endif
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
}
