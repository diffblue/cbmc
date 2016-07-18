/*******************************************************************\

Module: Global dependency analysis (field- and pointer-aware)

Author: Daniel Poetzl

\*******************************************************************/

#include "global_dependency_analysis.h"

#include <ctime>
#include <cstdlib>

levelt levelt::la(levelt::A);
levelt levelt::lb(levelt::B);
levelt levelt::lb0(levelt::B0);

elementt elementt::top(true);

const unsigned gda_max_num=10; // exclusive, must be >= 3
const unsigned gda_max_len=4; // inclusive, must be >= 2

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator<<(
  std::ostream &out,
  const levelt &level)
{
  switch(level.l)
  {
  case levelt::N:
    out << level.n;
    break;

  case levelt::A:
    out << "<ta>";
    break;

  case levelt::B:
    out << "<tb>";
    break;

  case levelt::B0:
    out << "<tb0>";
    break;

  default:
    assert(false);
    break;
  }

  return out;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// get ids of functions that could be used as threads
void global_dependency_analysist::get_thread_functions(
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

void global_dependency_analysist::get_returns(
  const goto_programt &goto_program,
  expr_vect &expr_vec, // expression used in the return
  location_sett &location_set) // return locations
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
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool global_dependency_analysist::handle_thread_create(
  locationt l, // pthread_create call
  const argumentst &args,
  location_sett &other_locations,
  abstract_symbolst &global)
{
  bool changed=false;

  unsigned thread_no=config.ansi_c.create_thread_arg_no_of_function;
  assert(thread_no<args.size());
  exprt thread=args[thread_no];

  unsigned arg_no=config.ansi_c.create_thread_arg_no_of_arg;
  argumentst arguments; // new arguments
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
      if(handle_function_call(id, l, lhs, arguments, other_locations, global))
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

    if(handle_function_call(id, l, lhs, arguments, other_locations, global))
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

bool global_dependency_analysist::is_handled(irep_idt id)
{
  std::string s=id2string(id);

  if(s.find("pthread_")!=0)
    return true; // handle all non-pthreads functions

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

bool global_dependency_analysist::handle_function_call(
  irep_idt id, // called function
  locationt l, // function call
  const exprt &lhs, // target of assignment of return value
  const argumentst &args, // args to function call
  location_sett &other_locations,
  abstract_symbolst &global) // symbols collected so far
{
  bool changed=false;

  abstract_symbolst tmp1(ns);
  abstract_symbolst tmp2(ns);

  goto_functionst::function_mapt::const_iterator cf_it
    =goto_functions.function_map.find(id);
  if(cf_it==goto_functions.function_map.end())
  {
    assert(false); // use remove_function_pointers
    return false;
  }

  const goto_functiont &goto_function=cf_it->second;
  if(!goto_function.body_available())
  {
    if(!is_handled(id))
      return false; // function call is ignored

    tmp1.from_expr(lhs);

    for(argumentst::const_iterator it=args.begin();
        it!=args.end(); it++)
    {
      tmp2.add_expr(*it);
    }

    changed|=global.handle_lhs(tmp1, tmp2);
    changed|=global.handle_rhs(tmp1, tmp2);

    return changed;
  }

  assert(goto_function.body_available());

#if 0
  const goto_programt &goto_program=goto_function.body;
#endif

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

    tmp1.clear();

    for(expr_vect::const_iterator it=expr_vec.begin();
        it!=expr_vec.end(); it++)
    {
      tmp1.add_expr(*it);
    }

    tmp2.from_expr(lhs);

    if(global.exists_covering(tmp2) ||
       global.exists_strict_covering(tmp1))
    {
      other_locations.insert(location_set.begin(), location_set.end());

      bool b=false;
      b|=global.merge(tmp1);
      b|=global.merge(tmp2);
      if(b)
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

#if 0
  if(args.size()!=pars.size())
  {
    std::cout << "called function: " << id << std::endl;
    std::cout << "call location number: " << l->location_number << std::endl;
    assert(false);
  }
#endif

  // handle all arguments
  unsigned n=args.size();
  for(unsigned i=0; i<n; i++)
  {
    const exprt &expr=args[i];

    tmp1.clear();
    tmp1.from_expr(expr);

    irep_idt par=pars[i];
    symbol_exprt symbol_expr(par);
    tmp2.clear();
    tmp2.from_expr(symbol_expr);

    changed|=global.handle_lhs(tmp2, tmp1);
    changed|=global.handle_rhs(tmp2, tmp1);
  }

  return changed;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void global_dependency_analysist::postprocess(
  location_sett &location_set, // dependent locations so far
  abstract_symbolst &global)
{
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
        const exprt &lhs=code.lhs();

        abstract_symbolst abstract_symbols(lhs, ns);
        if(abstract_symbols.exists_affects(global))
        {
          location_set.insert(i_it);
        }
      }
      else
      {
        location_set.insert(i_it);
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

void global_dependency_analysist::operator()(
  const expr_vect &expr_vec,
  location_sett &location_set) // output
{
  assert(!expr_vec.empty());
  assert(location_set.empty());
  assert(num_its==0);

  // symbols
  abstract_symbolst global(ns);
  abstract_symbolst tmp1(ns);
  abstract_symbolst tmp2(ns);

  // gather all symbols from starting expressions
  for(expr_vect::const_iterator it=expr_vec.begin();
      it!=expr_vec.end(); it++)
  {
    global.add_expr(*it);
  }

  if(global.empty())
    return;

  global.del_expr();

  assert(!global.prop_graph.empty());
  assert(global.prop_graph.is_base());

#if 1
  std::cout << "From base expressions: " << std::endl;
  global.output(std::cout);
  std::cout << std::endl;
#endif

  location_sett other_locations; // non-assignment locations

  bool changed;

  // do fixedpoint
  do
  {
    changed=false;
    num_its++;

#if 1
    std::cout << "Iteration: " << num_its << std::endl;
    std::cout << "Global size: " << global.size() << std::endl;
#endif

#if 0
    if(num_its==5)
    {
      // inspect random element
      srand(time(NULL));
      int r=rand();
      size_t idx=r%global.size();
      abstract_symbolst::as_sett::const_iterator it=global.as_set.begin();
      std::advance(it, idx);

      global.prop_graph.output(std::cout, *it);
      std::cout << std::endl;
      break;
    }
#endif

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
          // gather all symbols in the assignment
          const code_assignt &code=to_code_assign(i_it->code);
          const exprt &lhs=code.lhs();
          const exprt &rhs=code.rhs();

          tmp1.clear();
          tmp2.clear();
          tmp1.from_expr(lhs);
          tmp2.from_expr(rhs);

          changed|=global.handle_lhs(tmp1, tmp2);
          changed|=global.handle_rhs(tmp1, tmp2);
        }
        else if(i_it->is_function_call())
        {
          // get name of called function
          irep_idt id=misc::get_function_name(i_it);

          assert(!id.empty()); // use remove_function_pointers

          if(id.empty())
            continue;

          // get function call arguments
          code_function_callt code=to_code_function_call(i_it->code);
          argumentst args=code.arguments();

          // special handling for pthread_create
          if(id2string(id)==config.ansi_c.create_thread)
          {
            // we ignore the return value of pthread_create
            if(handle_thread_create(
                i_it, // function call location
                args, // args to pthread_create
                other_locations,
                global))
              changed=true;
          }
          else
          {
            // target of assignment
            const exprt &lhs=code.lhs();

            if(handle_function_call(
                id, // called function
                i_it, // function call location
                lhs, // target of assignment of return value
                args, // args to function call
                other_locations, // non-assignment locations
                global))
              changed=true;
          }
        }
      } // for all goto instructions
    } // for all goto functions
  } while(changed);

  assert(other_locations.empty());

  postprocess(location_set, global);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void global_dependency_analysist::compute_feasible(
  abstract_symbolst &feasible)
{
  assert(feasible.empty());

  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    // ignore vararg functions
    const code_typet &code_type=goto_function.type;
    if(code_type.has_ellipsis())
      continue;

    // function parameters
    std::vector<irep_idt> pars=goto_function.type.parameter_identifiers();
    for(std::vector<irep_idt>::const_iterator it=pars.begin();
        it!=pars.end(); it++)
    {
      irep_idt par=*it;
      symbol_exprt symbol_expr(par);

      feasible.add_expr(symbol_expr);
    }

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_assign())
      {
        const code_assignt &code=to_code_assign(i_it->code);
        const exprt &lhs=code.lhs();
        const exprt &rhs=code.rhs();

        feasible.add_expr(lhs);
        feasible.add_expr(rhs);
      }
      else if(i_it->is_function_call())
      {
        code_function_callt code=to_code_function_call(i_it->code);
        argumentst args=code.arguments();

        for(argumentst::const_iterator it=args.begin();
            it!=args.end(); it++)
        {
          feasible.add_expr(*it);
        }
      }
    }
  }

  assert(!feasible.prop_graph.empty());
  assert(feasible.prop_graph.is_base());
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void global_dependency_analysist::test1()
{
  typedef irep_idt idt;

  abstract_symbolt as1;
  abstract_symbolt as2;
  abstract_symbolt as3;

  as1.push_back(idt("x"), 1);
  assert(as1.length()==1);
  assert(!as1.empty());
  as2.push_back(idt("x"), 1);
  as3.push_back(idt("x"), 2);

  assert(as1.can_affect(as1));
  assert(as1.can_affect(as2));
  assert(!as3.can_affect(as2));
  assert(as2.can_affect(as3));

  assert(!as1.takes_address(as1));
  assert(!as2.takes_address(as1));
  assert(as2.takes_address(as3));
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void global_dependency_analysist::test2()
{
  typedef irep_idt idt;

  abstract_symbolt as1;
  abstract_symbolt as2;
  abstract_symbolt as3;
  abstract_symbolt as4;

  // set up symbols
  as1.push_back(idt("x"), levelt::la);
  assert(as1.length()==1);
  assert(!as1.empty());
  as2.push_back(idt("x"), levelt::lb);
  as3.push_back(idt("x"), levelt::lb0);
  as4.push_back(idt("x"), levelt(2));

  assert(as1.can_affect(as1));
  assert(as1.can_affect(as2));
  assert(as1.can_affect(as3));
  assert(!as1.can_affect(as4));
  assert(as4.can_affect(as1));

  assert(as1.takes_address(as1));
  assert(as1.takes_address(as2));
  assert(as1.takes_address(as3));
  assert(!as1.takes_address(as4));
  assert(as4.takes_address(as1));

}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void global_dependency_analysist::test3()
{
  typedef irep_idt idt;

  abstract_symbolst abss1(ns);
  abstract_symbolst abss2(ns);

  abstract_symbolt as1;
  abstract_symbolt as2;

  as1.push_back(idt("x"), 1);
  as2.push_back(idt("x"), 2);

  abss1.add(as1);
  assert(abss1.size()==1);
  abss2.add(as2);
  assert(abss2.size()==1);

  assert(abss1.exists_affects(abss1));
  assert(!abss1.exists_takes_address(abss1));

  assert(abss1.exists_affects(abss2));
  assert(abss1.exists_takes_address(abss2));
  assert(!abss2.exists_affects(abss1));

  abss1.merge(abss2);
  assert(abss1.size()==2);

  assert(abss2.exists_affects(abss1));
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void global_dependency_analysist::test4()
{
  typedef irep_idt idt;

  abstract_symbolst abss1(ns);
  abstract_symbolst abss2(ns);
  abstract_symbolst global(ns);

  abstract_symbolt as1;
  abstract_symbolt as2;
  abstract_symbolt as3;

  as1.push_back(idt("x"), 1);
  as2.push_back(idt("y"), 1);
  as3.push_back(idt("z"), 1);
  abss1.add(as1);
  abss2.add(as2);
  global.add(as3);

  bool changed=false;

  changed|=global.handle_lhs(abss1, abss2);
  changed|=global.handle_rhs(abss1, abss2);
  assert(!changed);
  assert(global.size()==1);

  global.add(as1);
  changed|=global.handle_lhs(abss1, abss2);
  changed|=global.handle_rhs(abss1, abss2);
  assert(changed);
  assert(global.size()==3);
}
