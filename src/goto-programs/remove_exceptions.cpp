/*******************************************************************\

Module: Remove exception handling 

Author: Cristina David

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove exception handling

#include "remove_exceptions.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <stack>
#include <algorithm>

#include <util/c_types.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

class remove_exceptionst
{
  typedef std::vector<std::pair<
    irep_idt, goto_programt::targett>> catch_handlerst;
  typedef std::vector<catch_handlerst> stack_catcht;

public:
  explicit remove_exceptionst(symbol_tablet &_symbol_table):
    symbol_table(_symbol_table)
  {
  }

  void operator()(
    goto_functionst &goto_functions);

protected:
  symbol_tablet &symbol_table;

  void add_exceptional_returns(
    const goto_functionst::function_mapt::iterator &);

  void instrument_exception_handler(
    const goto_functionst::function_mapt::iterator &,
    const goto_programt::instructionst::iterator &);

  void instrument_throw(
    const goto_functionst::function_mapt::iterator &,
    const goto_programt::instructionst::iterator &,
    const stack_catcht &,
    std::vector<exprt> &);

  void instrument_function_call(
    const goto_functionst::function_mapt::iterator &,
    const goto_programt::instructionst::iterator &,
    const stack_catcht &,
    std::vector<exprt> &);

  void instrument_exceptions(
    const goto_functionst::function_mapt::iterator &);
};

/// adds exceptional return variables for every function that may escape
/// exceptions
void remove_exceptionst::add_exceptional_returns(
  const goto_functionst::function_mapt::iterator &func_it)
{
  const irep_idt &function_id=func_it->first;
  goto_programt &goto_program=func_it->second.body;

  assert(symbol_table.has_symbol(function_id));
  const symbolt &function_symbol=symbol_table.lookup(function_id);

  // for now only add exceptional returns for Java
  if(function_symbol.mode!=ID_java)
    return;

  if(goto_program.empty())
    return;

  // the entry function has already been added to the symbol table
  // if you find it, initialise it
  if(symbol_table.has_symbol(id2string(function_id)+EXC_SUFFIX))
  {
    const symbolt &symbol=
      symbol_table.lookup(id2string(function_id)+EXC_SUFFIX);
    symbol_exprt lhs_expr_null=symbol.symbol_expr();
    null_pointer_exprt rhs_expr_null((pointer_typet(empty_typet())));
    goto_programt::targett t_null=
      goto_program.insert_before(goto_program.instructions.begin());
    t_null->make_assignment();
    t_null->source_location=
      goto_program.instructions.begin()->source_location;
    t_null->code=code_assignt(
      lhs_expr_null,
      rhs_expr_null);
    t_null->function=function_id;
    return;
  }

  // We generate an exceptional return value for any function that has
  // a throw or a function call. This can be improved by only considering
  // function calls that may escape exceptions. However, this will
  // require multiple passes.
  bool add_exceptional_var=false;
  forall_goto_program_instructions(instr_it, goto_program)
    if(instr_it->is_throw() || instr_it->is_function_call())
    {
      add_exceptional_var=true;
      break;
    }

  if(add_exceptional_var)
  {
    // look up the function symbol
    symbol_tablet::symbolst::iterator s_it=
      symbol_table.symbols.find(function_id);

    assert(s_it!=symbol_table.symbols.end());

    auxiliary_symbolt new_symbol;
    new_symbol.is_static_lifetime=true;
    new_symbol.module=function_symbol.module;
    new_symbol.base_name=id2string(function_symbol.base_name)+EXC_SUFFIX;
    new_symbol.name=id2string(function_symbol.name)+EXC_SUFFIX;
    new_symbol.mode=function_symbol.mode;
    new_symbol.type=pointer_type(empty_typet());
    symbol_table.add(new_symbol);

    // initialize the exceptional return with NULL
    symbol_exprt lhs_expr_null=new_symbol.symbol_expr();
    null_pointer_exprt rhs_expr_null(pointer_type(empty_typet()));
    goto_programt::targett t_null=
      goto_program.insert_before(goto_program.instructions.begin());
    t_null->make_assignment();
    t_null->source_location=
      goto_program.instructions.begin()->source_location;
    t_null->code=code_assignt(
      lhs_expr_null,
      rhs_expr_null);
    t_null->function=function_id;
  }
}

/// at the beginning of each handler in function f  adds exc=f#exception_value;
/// f#exception_value=NULL;
void remove_exceptionst::instrument_exception_handler(
  const goto_functionst::function_mapt::iterator &func_it,
  const goto_programt::instructionst::iterator &instr_it)
{
  const irep_idt &function_id=func_it->first;
  goto_programt &goto_program=func_it->second.body;

  assert(instr_it->type==CATCH && instr_it->code.has_operands());

  // retrieve the exception variable
  const exprt &exception=instr_it->code.op0();

  if(symbol_table.has_symbol(id2string(function_id)+EXC_SUFFIX))
  {
    const symbolt &function_symbol=
      symbol_table.lookup(id2string(function_id)+EXC_SUFFIX);
    // next we reset the exceptional return to NULL
    symbol_exprt lhs_expr_null=function_symbol.symbol_expr();
    null_pointer_exprt rhs_expr_null(pointer_type(empty_typet()));

    // add the assignment
    goto_programt::targett t_null=goto_program.insert_after(instr_it);
    t_null->make_assignment();
    t_null->source_location=instr_it->source_location;
    t_null->code=code_assignt(
      lhs_expr_null,
      rhs_expr_null);
    t_null->function=instr_it->function;

    // add the assignment exc=f#exception_value
    symbol_exprt rhs_expr_exc=function_symbol.symbol_expr();

    goto_programt::targett t_exc=goto_program.insert_after(instr_it);
    t_exc->make_assignment();
    t_exc->source_location=instr_it->source_location;
    t_exc->code=code_assignt(
      typecast_exprt(exception, rhs_expr_exc.type()),
      rhs_expr_exc);
    t_exc->function=instr_it->function;
  }
  instr_it->make_skip();
}

/// finds the instruction where the exceptional output is set or the end of the
/// function if no such output exists
static goto_programt::targett get_exceptional_output(
  goto_programt &goto_program)
{
  Forall_goto_program_instructions(it, goto_program)
  {
    const irep_idt &statement=it->code.get_statement();
    if(statement==ID_output)
    {
      assert(it->code.operands().size()>=2);
      const exprt &expr=it->code.op1();
      assert(expr.id()==ID_symbol);
      const symbol_exprt &symbol=to_symbol_expr(expr);
      if(id2string(symbol.get_identifier()).find(EXC_SUFFIX)
         !=std::string::npos)
        return it;
    }
  }
  return goto_program.get_end_function();
}

/// instruments each throw with conditional GOTOS to the  corresponding
/// exception handlers
void remove_exceptionst::instrument_throw(
  const goto_functionst::function_mapt::iterator &func_it,
  const goto_programt::instructionst::iterator &instr_it,
  const remove_exceptionst::stack_catcht &stack_catch,
  std::vector<exprt> &locals)
{
  assert(instr_it->type==THROW);

  goto_programt &goto_program=func_it->second.body;
  const irep_idt &function_id=func_it->first;

  assert(instr_it->code.operands().size()==1);

  // find the end of the function
  goto_programt::targett exceptional_output=
    get_exceptional_output(goto_program);
  if(exceptional_output!=instr_it)
  {
    // jump to the end of the function
    // this will appear after the GOTO-based dynamic dispatch below
    goto_programt::targett t_end=goto_program.insert_after(instr_it);
    t_end->make_goto(exceptional_output);
    t_end->source_location=instr_it->source_location;
    t_end->function=instr_it->function;
  }


  // find the symbol corresponding to the caught exceptions
  const symbolt &exc_symbol=
        symbol_table.lookup(id2string(function_id)+EXC_SUFFIX);
  symbol_exprt exc_thrown=exc_symbol.symbol_expr();

  // add GOTOs implementing the dynamic dispatch of the
  // exception handlers
  for(std::size_t i=stack_catch.size(); i-->0;)
  {
    for(std::size_t j=stack_catch[i].size(); j-->0;)
    {
      goto_programt::targett new_state_pc=
        stack_catch[i][j].second;

      // find handler
      goto_programt::targett t_exc=goto_program.insert_after(instr_it);
      t_exc->make_goto(new_state_pc);
      t_exc->source_location=instr_it->source_location;
      t_exc->function=instr_it->function;

      // use instanceof to check that this is the correct handler
      symbol_typet type(stack_catch[i][j].first);
      type_exprt expr(type);

      binary_predicate_exprt check(exc_thrown, ID_java_instanceof, expr);
      t_exc->guard=check;
    }
  }

  // add dead instructions
  for(const auto &local : locals)
  {
    goto_programt::targett t_dead=goto_program.insert_after(instr_it);
    t_dead->make_dead();
    t_dead->code=code_deadt(local);
    t_dead->source_location=instr_it->source_location;
    t_dead->function=instr_it->function;
  }

  // replace "throw x;" by "f#exception_value=x;"
  exprt exc_expr=instr_it->code;
  while(exc_expr.id()!=ID_symbol && exc_expr.has_operands())
    exc_expr=exc_expr.op0();

  // add the assignment with the appropriate cast
  code_assignt assignment(typecast_exprt(exc_thrown, exc_expr.type()),
                          exc_expr);
  // now turn the `throw' into `assignment'
  instr_it->type=ASSIGN;
  instr_it->code=assignment;
}

/// instruments each function call that may escape exceptions with conditional
/// GOTOS to the corresponding exception handlers
void remove_exceptionst::instrument_function_call(
  const goto_functionst::function_mapt::iterator &func_it,
  const goto_programt::instructionst::iterator &instr_it,
  const stack_catcht &stack_catch,
  std::vector<exprt> &locals)
{
  assert(instr_it->type==FUNCTION_CALL);

  goto_programt &goto_program=func_it->second.body;
  const irep_idt &function_id=func_it->first;

  // save the address of the next instruction
  goto_programt::instructionst::iterator next_it=instr_it;
  next_it++;

  code_function_callt &function_call=to_code_function_call(instr_it->code);
  assert(function_call.function().id()==ID_symbol);
  const irep_idt &callee_id=
    to_symbol_expr(function_call.function()).get_identifier();

  if(symbol_table.has_symbol(id2string(callee_id)+EXC_SUFFIX))
  {
    // we may have an escaping exception
    const symbolt &callee_exc_symbol=
      symbol_table.lookup(id2string(callee_id)+EXC_SUFFIX);
    symbol_exprt callee_exc=callee_exc_symbol.symbol_expr();

    // find the end of the function
    goto_programt::targett exceptional_output=
      get_exceptional_output(goto_program);
    if(exceptional_output!=instr_it)
    {
      // jump to the end of the function
      // this will appear after the GOTO-based dynamic dispatch below
      goto_programt::targett t_end=goto_program.insert_after(instr_it);
      t_end->make_goto(exceptional_output);
      t_end->source_location=instr_it->source_location;
      t_end->function=instr_it->function;
    }

    for(std::size_t i=stack_catch.size(); i-->0;)
    {
      for(std::size_t j=stack_catch[i].size(); j-->0;)
      {
        goto_programt::targett new_state_pc;
        new_state_pc=stack_catch[i][j].second;
        goto_programt::targett t_exc=goto_program.insert_after(instr_it);
        t_exc->make_goto(new_state_pc);
        t_exc->source_location=instr_it->source_location;
        t_exc->function=instr_it->function;
        // use instanceof to check that this is the correct handler
        symbol_typet type(stack_catch[i][j].first);
        type_exprt expr(type);
        binary_predicate_exprt check_instanceof(
          callee_exc,
          ID_java_instanceof,
          expr);
        t_exc->guard=check_instanceof;
      }
    }

    // add dead instructions
    for(const auto &local : locals)
    {
      goto_programt::targett t_dead=goto_program.insert_after(instr_it);
      t_dead->make_dead();
      t_dead->code=code_deadt(local);
      t_dead->source_location=instr_it->source_location;
      t_dead->function=instr_it->function;
    }

    // add a null check (so that instanceof can be applied)
    equal_exprt eq_null(
      callee_exc,
      null_pointer_exprt(pointer_type(empty_typet())));
    goto_programt::targett t_null=goto_program.insert_after(instr_it);
    t_null->make_goto(next_it);
    t_null->source_location=instr_it->source_location;
    t_null->function=instr_it->function;
    t_null->guard=eq_null;

    // after each function call g() in function f
    // adds f#exception_value=g#exception_value;
    const symbolt &caller=
      symbol_table.lookup(id2string(function_id)+EXC_SUFFIX);
    const symbol_exprt &lhs_expr=caller.symbol_expr();

    goto_programt::targett t=goto_program.insert_after(instr_it);
    t->make_assignment();
    t->source_location=instr_it->source_location;
    t->code=code_assignt(lhs_expr, callee_exc);
    t->function=instr_it->function;
  }
}

/// instruments throws, function calls that may escape exceptions and exception
/// handlers. Additionally, it re-computes the live-range of local variables in
/// order to add DEAD instructions.
void remove_exceptionst::instrument_exceptions(
  const goto_functionst::function_mapt::iterator &func_it)
{
  stack_catcht stack_catch; // stack of try-catch blocks
  std::vector<std::vector<exprt>> stack_locals; // stack of local vars
  std::vector<exprt> locals;
  goto_programt &goto_program=func_it->second.body;

  if(goto_program.empty())
    return;
  Forall_goto_program_instructions(instr_it, goto_program)
  {
    if(instr_it->is_decl())
    {
      code_declt decl=to_code_decl(instr_it->code);
      locals.push_back(decl.symbol());
    }
    // it's a CATCH but not a handler (as it has no operands)
    else if(instr_it->type==CATCH && !instr_it->code.has_operands())
    {
      if(instr_it->targets.empty()) // pop
      {
        // pop the local vars stack
        if(!stack_locals.empty())
        {
          locals=stack_locals.back();
          stack_locals.pop_back();
        }
        // pop from the stack if possible
        if(!stack_catch.empty())
        {
          stack_catch.pop_back();
        }
        else
        {
#ifdef DEBUG
          std::cout << "Remove exceptions: empty stack\n";
#endif
        }
      }
      else // push
      {
        stack_locals.push_back(locals);
        locals.clear();

        remove_exceptionst::catch_handlerst exception;
        stack_catch.push_back(exception);
        remove_exceptionst::catch_handlerst &last_exception=
          stack_catch.back();

        // copy targets
        const irept::subt &exception_list=
          instr_it->code.find(ID_exception_list).get_sub();
        assert(exception_list.size()==instr_it->targets.size());

        // Fill the map with the catch type and the target
        unsigned i=0;
        for(auto target : instr_it->targets)
        {
          last_exception.push_back(
            std::make_pair(exception_list[i].id(), target));
          i++;
        }
      }
      instr_it->make_skip();
    }
    // CATCH handler
    else if(instr_it->type==CATCH && instr_it->code.has_operands())
    {
      instrument_exception_handler(func_it, instr_it);
    }
    else if(instr_it->type==THROW)
    {
      instrument_throw(func_it, instr_it, stack_catch, locals);
    }
    else if(instr_it->type==FUNCTION_CALL)
    {
      instrument_function_call(func_it, instr_it, stack_catch, locals);
    }
  }
}

void remove_exceptionst::operator()(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    add_exceptional_returns(it);
  Forall_goto_functions(it, goto_functions)
    instrument_exceptions(it);
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_exceptionst remove_exceptions(symbol_table);
  remove_exceptions(goto_functions);
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions(goto_modelt &goto_model)
{
  remove_exceptionst remove_exceptions(goto_model.symbol_table);
  remove_exceptions(goto_model.goto_functions);
}
