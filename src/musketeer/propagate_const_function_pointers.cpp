#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/irep.h>
#include <util/hash_cont.h>
#include <util/i2string.h>
#include <util/namespace.h>
#include <util/message.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>

#include <map>
#include <list>
#include <cassert>

class const_function_pointer_propagationt {
protected:
  symbol_tablet& symbol_table;
  goto_functionst& goto_functions;
  const namespacet ns;
  messaget& message;

  hash_map_cont<irep_idt, unsigned, irep_id_hash> map_unique;

  /* maps const pointer to function (expression + arguments at call)  */
  hash_map_cont<irep_idt, symbol_exprt, irep_id_hash> pointer_to_fun;

  /* maps const pointer to where it was defined in the call function stack */
  hash_map_cont<irep_idt, unsigned, irep_id_hash> pointer_to_stack;

  /* where a const function to inline was the first time invoked */
  hash_map_cont<irep_idt, unsigned, irep_id_hash> fun_id_to_invok;

  /* stack of callsites: provides functions and location in the goto-program */
  goto_programt::const_targetst callsite_stack;

  bool resolve(const irep_idt& symb, 
    symbol_exprt& goto_function, 
    unsigned& stack_scope) 
  {
    message.debug() << "I resolve " << symb << " with " 
      << pointer_to_fun[symb].get_identifier() << messaget::eom;
    if(pointer_to_fun.find(symb)==pointer_to_fun.end())
      return false;
    else {
      goto_function=pointer_to_fun[symb];
      stack_scope=pointer_to_stack[symb];
      return true;
    }
  }

  /* TODO: use the whole name rather than the base one, to avoid 
     overwriting?
     Yes! Pure propagation of pointers only intra-proc. At call, arguments
     and pointed functions stored in the table -- no need to keep the match
     between two pointers inter-proc. */
  bool add(const irep_idt& symb, const symbol_exprt& goto_function) 
  {
    return add(symb, goto_function, callsite_stack.size());
  }

  bool add(const irep_idt& symb, 
    const symbol_exprt& goto_function,
    unsigned scope) 
  {
    pointer_to_fun[symb]=goto_function;
    pointer_to_stack[symb]=scope;

    const symbolt& function_symb=ns.lookup(goto_function.get_identifier());
    if(fun_id_to_invok.find(function_symb.base_name)==fun_id_to_invok.end())
      fun_id_to_invok[function_symb.base_name]=scope;

    return true;
  }

  bool remove(const irep_idt& symb) {
    //assert(pointer_to_fun.find(symb)!=pointer_to_fun.end());
    pointer_to_fun.erase(symb);
    return true;
  }

  bool has(const irep_idt& symb) const {
    return pointer_to_fun.find(symb)!=pointer_to_fun.end();
  }

  symbol_exprt get(const irep_idt& symb) {
    return pointer_to_fun[symb];
  }

  /* to keep track of the visited functions and avoid recursion */
  std::set<irep_idt> functions_met;

  void propagate(const irep_idt& function);

  void dup_caller_and_inline_callee(const symbol_exprt& function, 
    unsigned stack_scope);

  /* to keep track of the constant function pointers passed as arguments */
  class arg_stackt: public std::set<irep_idt>
  {
  protected:
    const_function_pointer_propagationt& cfpp;

  public:
    arg_stackt (const_function_pointer_propagationt& _cfpp)
      :cfpp(_cfpp)
    {}
    void add_args(const symbol_exprt& const_function, 
      goto_programt::instructionst::iterator it);
    void remove_args();
  };

public:
  const_function_pointer_propagationt(symbol_tablet& _symbol_table, 
    goto_functionst& _goto_functions, messaget& _message)
    :symbol_table(_symbol_table), goto_functions(_goto_functions), 
      ns(_symbol_table), message(_message)
  {}

  /* Note that it only propagates from MAIN, following the CFG, without
     resolving non-constant function pointers. */ 
  void propagate() {
    propagate(goto_functionst::entry_point());
  }
};

/*******************************************************************\

Function:

  Inputs: 'it' pointing to the callsite to update, 'function' the function 
          actually called, 'stack_scope' the place where the constant was
          defined in the call stack

 Outputs:

 Purpose:

\*******************************************************************/

void const_function_pointer_propagationt::dup_caller_and_inline_callee(
  const symbol_exprt& const_function,
  unsigned stack_scope)
{
  assert(callsite_stack.size()>0);

  /* for the reconstruction of the {call,callsite}_stacks after the
     duplication */
  goto_programt::const_targetst new_callsite_stack;

  goto_programt::const_targetst::const_iterator 
    callsite=callsite_stack.begin();

  std::string last_suffix="";

  for(unsigned current_call=callsite_stack.size(); 
    current_call>=stack_scope; 
    --current_call)
  {
    message.debug() << "current_call=" << current_call << " stack_scope=" 
      << stack_scope << " callsite_stack.size()=" << callsite_stack.size() 
      << messaget::eom;
    assert(callsite!=callsite_stack.end());

    message.debug() << callsite_stack.size() << messaget::eom;

    const irep_idt function_id=(*callsite)->function;

    goto_functionst::goto_functiont* pfunction_dup=&goto_functions
      .function_map[function_id];
    
    std::string suffix="$";

    if(current_call>stack_scope)
    {
      /* unique suffix */
      if(map_unique.find(function_id)!=map_unique.end()) {
        suffix+=i2string(map_unique[function_id]);
        ++map_unique[function_id];
      }
      else {
        map_unique[function_id]=0;
        suffix+=i2string(map_unique[function_id]);
        ++map_unique[function_id];
      }

      /* creates a new, unique copy of the function */
      message.debug() << "duplicate function: " << function_id 
        << messaget::eom;
      const irep_idt function_new_id=id2string(function_id)+suffix;

      goto_functionst::goto_functiont& function_dup=
        goto_functions.function_map[function_new_id];
      function_dup.copy_from(goto_functions.function_map[function_id]);
      pfunction_dup=&function_dup;

      for(goto_programt::targett it=function_dup.body.instructions.begin();
        it!=function_dup.body.instructions.end(); ++it)
        it->function=function_new_id;

      assert(goto_functions.function_map[function_new_id].body.instructions.size()>0);

      /* removes in definition the argument leading to the const_function */
      code_typet::parameterst& args=function_dup.type.parameters();
      for(code_typet::parameterst::iterator it=args.begin();
        it!=args.end(); ++it)
      {
        if(pointer_to_fun.find(it->get_identifier())!=pointer_to_fun.end()
          && pointer_to_fun[it->get_identifier()]==const_function)
          args.erase(it);
      }

      /* updates the table of symbols */
      const symbolt& fun_symb=ns.lookup(function_id);
      symbolt dup_fun_symb;
      dup_fun_symb=fun_symb;
      dup_fun_symb.name=id2string(dup_fun_symb.name)+suffix;
      dup_fun_symb.base_name=id2string(dup_fun_symb.base_name)+suffix;
      dup_fun_symb.pretty_name=id2string(dup_fun_symb.pretty_name)+suffix;
      symbol_table.add(dup_fun_symb);

      goto_functions.update();
      message.debug() << "new function " << function_new_id << " created." 
        << messaget::eom;
      message.debug() << "new function " 
        << goto_functions.function_map[function_new_id].body.instructions
          .front().function << " created." << messaget::eom;
    }

    if(current_call<callsite_stack.size()) 
    {
      message.debug() << "we then modify the previous callers" 
        << messaget::eom;

      /* sets the call to the previous newly duplicated function */
      goto_programt::instructionst& new_instructions=
        pfunction_dup->body.instructions;
      goto_programt::targett it=new_instructions.begin();
      // beurk -- should use location_number or something unique per 
      // instruction but shared between two copies of a same goto-program
      for(; it->source_location!=(*callsite)->source_location 
        && it!=new_instructions.end(); ++it);
      
      assert(it->source_location==(*callsite)->source_location);
      exprt& function_called=to_code_function_call(it->code).function();
      assert(function_called.id()==ID_symbol);
      symbol_exprt& symbol_fun_called=to_symbol_expr(function_called);
      symbol_fun_called.set_identifier(
        id2string(symbol_fun_called.get_identifier())+last_suffix);

      /* removes the constant pointer from the arguments passed at call */ 
      code_function_callt::argumentst& args=to_code_function_call(it->code)
        .arguments();
      for(code_function_callt::argumentst::iterator arg_it=args.begin();
        arg_it!=args.end(); ++arg_it)
      {
        if(arg_it->id()==ID_symbol) {
          const symbol_exprt& symb_arg=to_symbol_expr(*arg_it);
          if(symb_arg.get_identifier()==const_function.get_identifier()
            || (pointer_to_fun.find(symb_arg.get_identifier())
              !=pointer_to_fun.end() 
              && pointer_to_fun[symb_arg.get_identifier()]==const_function) )
            args.erase(arg_it);
        }
        else if(arg_it->id()==ID_address_of) {
          const address_of_exprt& add_arg=to_address_of_expr(*arg_it);
          if(add_arg.object().id()==ID_symbol 
            && to_symbol_expr(add_arg.object()).get_identifier()
              ==const_function.get_identifier())
            args.erase(arg_it);
        }
      }

      new_callsite_stack.push_back(it); 
    }
    else {
      message.debug() << "we first modify the first caller" << messaget::eom;

      /* initially, inlines the callee function in the duplicate of the last
         caller */
      goto_programt::instructionst& new_instructions=
        pfunction_dup->body.instructions;
      goto_programt::targett it=new_instructions.begin();
      // beurk -- should use location_number or something unique per 
      // instruction but shared between two copies of a same goto-program
      for(; it->source_location!=(*callsite)->source_location 
        && it!=new_instructions.end(); ++it); 

      message.debug() << "callsite targetted: " << (*callsite)->source_location
        << " function: " << const_function.get_identifier() << messaget::eom;

      assert(it->source_location==(*callsite)->source_location);
      message.debug() << it->code.get_statement() << messaget::eom;
      to_code_function_call(it->code).function()=const_function;

      new_callsite_stack.push_back(it);
    }

    last_suffix=suffix;
    ++callsite;
  }

  /* and updates the call_stack and callsite_stack */
  //new_callsite_stack.splice(new_callsite_stack.end(), callsite_stack, 
  //  callsite, callsite_stack.end());
  for(goto_programt::const_targetst::const_iterator it=callsite; 
    it!=callsite_stack.end(); ++it)
    new_callsite_stack.push_back(*it);

  assert(callsite_stack.size()==new_callsite_stack.size());
  callsite_stack.swap(new_callsite_stack);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose: adds const pointers (instantiated here or propagated) passed 
          as arguments in the map

\*******************************************************************/

void const_function_pointer_propagationt::arg_stackt::add_args(
  const symbol_exprt& const_function, 
  goto_programt::instructionst::iterator it)
{
  /* if constant pointers passed as arguments, add the names of the parameters
     in the function definition to the map */
  const code_function_callt::argumentst& arg=
    to_code_function_call(it->code).arguments();

  /* retrieve the corresponding parameters expressions in the
     function definition */
  assert(cfpp.goto_functions.function_map.find(
    const_function.get_identifier())!=cfpp.goto_functions.function_map.end());

  goto_functionst::goto_functiont& cor_function=
    cfpp.goto_functions.function_map[const_function.get_identifier()];

  code_typet::parameterst::const_iterator cor_arg_it=
    cor_function.type.parameters().begin();

  for(code_function_callt::argumentst::const_iterator arg_it=arg.begin();
    arg_it!=arg.end();
    ++arg_it, ++cor_arg_it)
  {
    assert(cor_arg_it!=cor_function.type.parameters().end());

    if(arg_it->id()!=ID_symbol && arg_it->id()!=ID_address_of)
      continue;

    if(arg_it->id()==ID_address_of) {
      if(to_address_of_expr(*arg_it).object().id()!=ID_symbol)
        continue;

      const exprt& arg_expr=to_address_of_expr(*arg_it).object();
      assert(arg_expr.id()==ID_symbol);
      const symbol_exprt& arg_symbol_expr=to_symbol_expr(arg_expr);

      //const symbolt& arg_symbol=
        //cfpp.symbol_table.lookup(arg_symbol_expr.get_identifier());

      // debug
      for(hash_map_cont<irep_idt, unsigned, irep_id_hash>::const_iterator
        it=cfpp.fun_id_to_invok.begin();
        it!=cfpp.fun_id_to_invok.end();
        ++it)
        cfpp.message.debug() << it->first << ":" << it->second << " ";
     cfpp.message.debug() << messaget::eom;

      cfpp.add(cor_arg_it->get_base_name(), arg_symbol_expr);
      insert(cor_arg_it->get_base_name());
      cfpp.message.debug() << "SET: insert " << cor_arg_it->get_base_name() 
        << messaget::eom;
    }
    else {
      cfpp.message.debug() << "fun: " << const_function.get_identifier() 
        << " - arg: (symb) " << cfpp.symbol_table
          .lookup(to_symbol_expr(*arg_it).get_identifier()).base_name 
        << messaget::eom;

      const symbol_exprt& arg_symbol_expr=to_symbol_expr(*arg_it);
      const symbolt& arg_symbol=
        cfpp.symbol_table.lookup(arg_symbol_expr.get_identifier());

      if(cfpp.has(arg_symbol.base_name)) {
        cfpp.add(cor_arg_it->get_base_name(), cfpp.get(arg_symbol.base_name),
          cfpp.fun_id_to_invok[arg_symbol.base_name]);
        insert(cor_arg_it->get_base_name());
        cfpp.message.debug() << "SET: insert " << cor_arg_it->get_base_name() 
          << messaget::eom;
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

void const_function_pointer_propagationt::arg_stackt::remove_args() {
  /* remove the parameter names */
  for(const_iterator arg_it=begin(); arg_it!=end(); ++arg_it) {
    cfpp.remove(*arg_it);
    cfpp.message.debug() << "SET: remove " << *arg_it << messaget::eom;
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void const_function_pointer_propagationt::propagate(
  const irep_idt& function_id) 
{
  if(goto_functions.function_map.find(function_id)
    ==goto_functions.function_map.end())
    return;

  goto_functionst::goto_functiont& function=
    goto_functions.function_map[function_id];

  if(functions_met.find(function_id)!=functions_met.end())
   return;

  functions_met.insert(function_id);

  Forall_goto_program_instructions(it, function.body)
  {
    if(it->is_assign()) {
      /* is it an assignment of function pointer? */
      const code_assignt& assign=to_code_assign(it->code);
      const exprt& lhs=assign.lhs();
      const exprt& rhs=assign.rhs();

      /* rhs has to be an address to a function */
      if(rhs.id()!=ID_address_of)
        continue;
      const address_of_exprt& addr_rhs=to_address_of_expr(rhs);

      if(addr_rhs.object().id()!=ID_symbol 
        || addr_rhs.object().type().id()!=ID_code)
        continue;
      const symbol_exprt& symbol_rhs=to_symbol_expr(addr_rhs.object());

      /* lhs must be a pointer */        
      if(lhs.id()!=ID_symbol || lhs.type().id()!=ID_pointer)
        continue;
      const symbol_exprt& symbol_expr_lhs=to_symbol_expr(lhs);
      const symbolt& symbol_lhs=
        symbol_table.lookup(symbol_expr_lhs.get_identifier());

      add(symbol_lhs.base_name, symbol_rhs);
    }
    else if(it->is_function_call()) {
      callsite_stack.push_front(it);

      const exprt& fun=to_code_function_call(it->code).function();
 
      /* if it is a function pointer */
      if(fun.id()==ID_dereference) {
        const exprt& fun_pointer=to_dereference_expr(fun).pointer();
        if(fun_pointer.id()!=ID_symbol) {
          callsite_stack.pop_front();
          continue;
        }

        const symbol_exprt& fun_symbol_expr=to_symbol_expr(fun_pointer);
        const symbolt& fun_symbol=
          symbol_table.lookup(fun_symbol_expr.get_identifier());
        symbol_exprt const_function;
        unsigned stack_scope=0;

        /* is it a constant pointer? */
        if(resolve(fun_symbol.base_name, const_function, stack_scope)) 
        {
          /* saves the current context (stack of --unduplicated-- callsites) */
          goto_programt::const_targetst context(callsite_stack);

          /* it is. Inline it and explore it. */
          dup_caller_and_inline_callee(const_function, stack_scope);
          message.debug() << "I substitute " << const_function.get_identifier() 
            << messaget::eom;

          arg_stackt arg_stack(*this);
          arg_stack.add_args(const_function, it);

          propagate(const_function.get_identifier());

          arg_stack.remove_args();

          /* restores the context */
          callsite_stack.swap(context);
        }
        else {
          /* no. Ignore it and leave it to the remove_function_pointers */
        }
      }
      else if(fun.id()==ID_symbol) {
        message.debug() << "Propagates through " << to_symbol_expr(fun)
          .get_identifier() << messaget::eom;

        /* just propagate */
        const symbol_exprt& fun_symbol_expr=to_symbol_expr(fun);
        const irep_idt& fun_id=fun_symbol_expr.get_identifier(); 

        arg_stackt arg_stack(*this);
        arg_stack.add_args(fun_symbol_expr, it);

        propagate(fun_id);

        arg_stack.remove_args();
      }

      callsite_stack.pop_front();
    }
    else if(it->is_end_function()) {
      functions_met.erase(function_id);
      return;
    }
  }

  functions_met.erase(function_id);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void propagate_const_function_pointers(
  symbol_tablet& symbol_table,
  goto_functionst& goto_functions, 
  message_handlert& message_handler)
{
  messaget message(message_handler);
  const_function_pointer_propagationt propagation(symbol_table, 
    goto_functions, message);
  propagation.propagate();
  goto_functions.update();
}

