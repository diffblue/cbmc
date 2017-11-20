/*******************************************************************\

Module: Remove Instance-of Operators

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Remove Instance-of Operators

#include "remove_instanceof.h"

#include "class_hierarchy.h"
#include "class_identifier.h"

#include <util/fresh_symbol.h>
#include <java_bytecode/java_types.h>

#include <sstream>

class remove_instanceoft
{
public:
  explicit remove_instanceoft(symbol_tablet &symbol_table)
  : symbol_table(symbol_table), ns(symbol_table)
  {
    class_hierarchy(symbol_table);
  }

  // Lower instanceof for a single functions
  bool lower_instanceof(goto_programt &);

protected:
  symbol_tablet &symbol_table;
  namespacet ns;
  class_hierarchyt class_hierarchy;

  bool lower_instanceof(goto_programt &, goto_programt::targett);

  std::size_t lower_instanceof(
    exprt &, goto_programt &, goto_programt::targett);
};

/// Replaces an expression like e instanceof A with e.\@class_identifier == "A"
/// or a big-or of similar expressions if we know of subtypes that also satisfy
/// the given test.
/// \param expr: Expression to lower (the code or the guard of an instruction)
/// \param goto_program: program the expression belongs to
/// \param this_inst: instruction the expression is found at
/// \return number of instanceof expressions that have been replaced
std::size_t remove_instanceoft::lower_instanceof(
  exprt &expr,
  goto_programt &goto_program,
  goto_programt::targett this_inst)
{
  if(expr.id()!=ID_java_instanceof)
  {
    std::size_t replacements=0;
    Forall_operands(it, expr)
      replacements+=lower_instanceof(*it, goto_program, this_inst);
    return replacements;
  }

  INVARIANT(
    expr.operands().size()==2,
    "java_instanceof should have two operands");

  const exprt &check_ptr=expr.op0();
  INVARIANT(
    check_ptr.type().id()==ID_pointer,
    "instanceof first operand should be a pointer");

  const exprt &target_arg=expr.op1();
  INVARIANT(
    target_arg.id()==ID_type,
    "instanceof second operand should be a type");
  const typet &target_type=target_arg.type();

  // Find all types we know about that satisfy the given requirement:
  INVARIANT(
    target_type.id()==ID_symbol,
    "instanceof second operand should have a simple type");
  const irep_idt &target_name=
    to_symbol_type(target_type).get_identifier();
  std::vector<irep_idt> children=
    class_hierarchy.get_children_trans(target_name);
  children.push_back(target_name);

  // Insert an instruction before the new check that assigns the clsid we're
  // checking for to a temporary, as GOTO program if-expressions should
  // not contain derefs.
  // We actually insert the assignment instruction after the existing one.
  // This will briefly be ill-formed (use before def of instanceof_tmp) but the
  // two will subsequently switch places. This makes sure that the inserted
  // assignement doesn't end up before any labels pointing at this instruction.
  symbol_typet jlo=to_symbol_type(java_lang_object_type().subtype());
  exprt object_clsid=get_class_identifier_field(check_ptr, jlo, ns);

  symbolt &newsym=
    get_fresh_aux_symbol(
      object_clsid.type(),
      "instanceof_tmp",
      "instanceof_tmp",
      source_locationt(),
      ID_java,
      symbol_table);

  auto newinst=goto_program.insert_after(this_inst);
  newinst->make_assignment();
  newinst->code=code_assignt(newsym.symbol_expr(), object_clsid);
  newinst->source_location=this_inst->source_location;
  newinst->function=this_inst->function;

  // Replace the instanceof construct with a big-or.
  exprt::operandst or_ops;
  for(const auto &clsname : children)
  {
    constant_exprt clsexpr(clsname, string_typet());
    equal_exprt test(newsym.symbol_expr(), clsexpr);
    or_ops.push_back(test);
  }
  expr=disjunction(or_ops);

  return 1;
}

/// Replaces expressions like e instanceof A with e.\@class_identifier == "A"
/// or a big-or of similar expressions if we know of subtypes that also satisfy
/// the given test. Does this for the code or guard at a specific instruction.
/// \param goto_program: program to process
/// \param target: instruction to check for instanceof expressions
/// \return true if an instanceof has been replaced
bool remove_instanceoft::lower_instanceof(
  goto_programt &goto_program,
  goto_programt::targett target)
{
  std::size_t replacements=
    lower_instanceof(target->code, goto_program, target)+
    lower_instanceof(target->guard, goto_program, target);

  if(replacements==0)
    return false;
  // Swap the original instruction with the last assignment added after it
  target->swap(*std::next(target, replacements));
  return true;
}

/// Replace every instanceof in the passed function body with an explicit
/// class-identifier test.
/// Extra auxiliary variables may be introduced into symbol_table.
/// \param goto_program: The function body to work on.
/// \return true if one or more instanceof expressions have been replaced
bool remove_instanceoft::lower_instanceof(goto_programt &goto_program)
{
  bool changed=false;
  for(goto_programt::instructionst::iterator target=
      goto_program.instructions.begin();
    target!=goto_program.instructions.end();
    ++target)
  {
    changed=lower_instanceof(goto_program, target) || changed;
  }
  if(!changed)
    return false;
  goto_program.update();
  return true;
}


/// Replace every instanceof in the passed function with an explicit
/// class-identifier test.
/// Extra auxiliary variables may be introduced into symbol_table.
/// \param function: The function to work on.
/// \param symbol_table: The symbol table to add symbols to.
void remove_instanceof(
  goto_functionst::goto_functiont &function,
  symbol_tablet &symbol_table)
{
  remove_instanceoft rem(symbol_table);
  rem.lower_instanceof(function.body);
}

/// Replace every instanceof in every function with an explicit
/// class-identifier test.
/// Extra auxiliary variables may be introduced into symbol_table.
/// \param goto_functions: The functions to work on.
/// \param symbol_table: The symbol table to add symbols to.
void remove_instanceof(
  goto_functionst &goto_functions,
  symbol_tablet &symbol_table)
{
  remove_instanceoft rem(symbol_table);
  bool changed=false;
  for(auto &f : goto_functions.function_map)
    changed=rem.lower_instanceof(f.second.body) || changed;
  if(changed)
    goto_functions.compute_location_numbers();
}

void remove_instanceof(goto_modelt &goto_model)
{
  remove_instanceof(goto_model.goto_functions, goto_model.symbol_table);
}
