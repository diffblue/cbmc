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

#include <sstream>

class remove_instanceoft
{
public:
  remove_instanceoft(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions):
    symbol_table(_symbol_table),
    ns(_symbol_table),
    goto_functions(_goto_functions)
  {
    class_hierarchy(_symbol_table);
  }

  // Lower instanceof for all functions:
  void lower_instanceof();

protected:
  symbol_tablet &symbol_table;
  namespacet ns;
  class_hierarchyt class_hierarchy;
  goto_functionst &goto_functions;

  bool lower_instanceof(goto_programt &);

  typedef std::vector<
    std::pair<goto_programt::targett, goto_programt::targett>> instanceof_instt;

  void lower_instanceof(
    goto_programt &,
    goto_programt::targett,
    instanceof_instt &);

  void lower_instanceof(
    exprt &,
    goto_programt &,
    goto_programt::targett,
    instanceof_instt &);

  bool contains_instanceof(const exprt &);
};

/// Avoid breaking sharing by checking for instanceof before calling
/// lower_instanceof.
/// \par parameters: Expression `expr`
/// \return Returns true if `expr` contains any instanceof ops
bool remove_instanceoft::contains_instanceof(
  const exprt &expr)
{
  if(expr.id()==ID_java_instanceof)
    return true;
  forall_operands(it, expr)
    if(contains_instanceof(*it))
      return true;
  return false;
}

/// Replaces an expression like e instanceof A with e.\@class_identifier == "A"
/// or a big-or of similar expressions if we know of subtypes that also satisfy
/// the given test.
/// \param expr: Expression to lower (the code or the guard of an instruction)
/// \param goto_program: program the expression belongs to
/// \param this_inst: instruction the expression is found at
/// \param inst_switch: set of instructions to switch around once we're done
void remove_instanceoft::lower_instanceof(
  exprt &expr,
  goto_programt &goto_program,
  goto_programt::targett this_inst,
  instanceof_instt &inst_switch)
{
  if(expr.id()!=ID_java_instanceof)
  {
    Forall_operands(it, expr)
      lower_instanceof(*it, goto_program, this_inst, inst_switch);
    return;
  }

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
    symbol_typet jlo("java::java.lang.Object");
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

    // Remember to switch the instructions
    inst_switch.push_back(make_pair(this_inst, newinst));
    // Replace the instanceof construct with a big-or.
    exprt::operandst or_ops;
    for(const auto &clsname : children)
    {
      constant_exprt clsexpr(clsname, string_typet());
      equal_exprt test(newsym.symbol_expr(), clsexpr);
      or_ops.push_back(test);
    }
    expr=disjunction(or_ops);
}

/// Replaces expressions like e instanceof A with e.\@class_identifier == "A"
/// or a big-or of similar expressions if we know of subtypes that also satisfy
/// the given test. Does this for the code or guard at a specific instruction.
/// \param goto_program: program to process
/// \param target: instruction to check for instanceof expressions
/// \param inst_switch: set of instructions to switch around once we're done
void remove_instanceoft::lower_instanceof(
  goto_programt &goto_program,
  goto_programt::targett target,
  instanceof_instt &inst_switch)
{
  bool code_iof=contains_instanceof(target->code);
  bool guard_iof=contains_instanceof(target->guard);
  // The instruction-switching step below will malfunction if a check
  // has been added for the code *and* for the guard. This should
  // be impossible, because guarded instructions currently have simple
  // code (e.g. a guarded-goto), but this assertion checks that this
  // assumption is correct and remains true on future evolution of the
  // allowable goto instruction types.
  INVARIANT(
    !(code_iof && guard_iof), "instanceof code should not have a guard");
  if(code_iof)
    lower_instanceof(target->code, goto_program, target, inst_switch);
  if(guard_iof)
    lower_instanceof(target->guard, goto_program, target, inst_switch);
}

/// Replace every instanceof in the passed function body with an explicit
/// class-identifier test.
/// Extra auxiliary variables may be introduced into symbol_table.
/// \param goto_program: The function body to work on.
/// \return true if one or more instanceof expressions have been replaced
bool remove_instanceoft::lower_instanceof(goto_programt &goto_program)
{
  instanceof_instt inst_switch;
  for(goto_programt::instructionst::iterator target=
      goto_program.instructions.begin();
    target!=goto_program.instructions.end();
    ++target)
  {
    lower_instanceof(goto_program, target, inst_switch);
  }
  if(inst_switch.empty())
    return false;
  for(auto &p : inst_switch)
  {
    const goto_programt::targett &this_inst=p.first;
    const goto_programt::targett &newinst=p.second;
    this_inst->swap(*newinst);
  }
  goto_program.update();
  return true;
}

/// See function above
/// \return Side-effects on this->goto_functions, replacing every instanceof in
///   every function with an explicit test.
void remove_instanceoft::lower_instanceof()
{
  bool changed=false;
  for(auto &f : goto_functions.function_map)
    changed=(lower_instanceof(f.second.body) || changed);
  if(changed)
    goto_functions.compute_location_numbers();
}

/// See function above
/// \par parameters: `goto_functions`, a function map, and the corresponding
/// `symbol_table`.
/// \return Side-effects on goto_functions, replacing every instanceof in every
///   function with an explicit test. Extra auxiliary variables may be
///   introduced into `symbol_table`.
void remove_instanceof(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_instanceoft rem(symbol_table, goto_functions);
  rem.lower_instanceof();
}

void remove_instanceof(goto_modelt &goto_model)
{
  remove_instanceof(goto_model.symbol_table, goto_model.goto_functions);
}
