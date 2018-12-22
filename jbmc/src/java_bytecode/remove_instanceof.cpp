/*******************************************************************\

Module: Remove Instance-of Operators

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Remove Instance-of Operators

#include "remove_instanceof.h"

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/class_identifier.h>
#include <goto-programs/goto_convert.h>

#include <util/fresh_symbol.h>
#include <java_bytecode/java_types.h>

#include <sstream>

class remove_instanceoft
{
public:
  remove_instanceoft(
    symbol_table_baset &symbol_table,
    const class_hierarchyt &class_hierarchy,
    message_handlert &message_handler)
    : symbol_table(symbol_table),
      class_hierarchy(class_hierarchy),
      ns(symbol_table),
      message_handler(message_handler)
  {
  }

  // Lower instanceof for a single function
  bool lower_instanceof(goto_programt &);

  // Lower instanceof for a single instruction
  bool lower_instanceof(goto_programt &, goto_programt::targett);

protected:
  symbol_table_baset &symbol_table;
  const class_hierarchyt &class_hierarchy;
  namespacet ns;
  message_handlert &message_handler;

  bool lower_instanceof(
    exprt &, goto_programt &, goto_programt::targett);
};

/// Replaces an expression like e instanceof A with e.\@class_identifier == "A"
/// or a big-or of similar expressions if we know of subtypes that also satisfy
/// the given test.
/// \param expr: Expression to lower (the code or the guard of an instruction)
/// \param goto_program: program the expression belongs to
/// \param this_inst: instruction the expression is found at
/// \return true if any instanceof instructionw was replaced
bool remove_instanceoft::lower_instanceof(
  exprt &expr,
  goto_programt &goto_program,
  goto_programt::targett this_inst)
{
  if(expr.id()!=ID_java_instanceof)
  {
    bool changed = false;
    Forall_operands(it, expr)
      changed |= lower_instanceof(*it, goto_program, this_inst);
    return changed;
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
    target_type.id() == ID_struct_tag,
    "instanceof second operand should have a simple type");
  const irep_idt &target_name =
    to_struct_tag_type(target_type).get_identifier();
  std::vector<irep_idt> children=
    class_hierarchy.get_children_trans(target_name);
  children.push_back(target_name);
  // Sort alphabetically to make order of generated disjuncts
  // independent of class loading order
  std::sort(
    children.begin(), children.end(), [](const irep_idt &a, const irep_idt &b) {
      return a.compare(b) < 0;
    });

  // Make temporaries to store the class identifier (avoids repeated derefs) and
  // the instanceof result:

  auto jlo = to_struct_tag_type(java_lang_object_type().subtype());
  exprt object_clsid = get_class_identifier_field(check_ptr, jlo, ns);

  symbolt &clsid_tmp_sym = get_fresh_aux_symbol(
    object_clsid.type(),
    id2string(this_inst->function),
    "class_identifier_tmp",
    source_locationt(),
    ID_java,
    symbol_table);

  symbolt &instanceof_result_sym = get_fresh_aux_symbol(
    bool_typet(),
    id2string(this_inst->function),
    "instanceof_result_tmp",
    source_locationt(),
    ID_java,
    symbol_table);

  // Create
  // if(expr == null)
  //   instanceof_result = false;
  // else
  //   string clsid = expr->@class_identifier
  //   instanceof_result = clsid == "A" || clsid == "B" || ...

  // According to the Java specification, null instanceof T is false for all
  // possible values of T.
  // (http://docs.oracle.com/javase/specs/jls/se7/html/jls-15.html#jls-15.20.2)

  code_blockt else_block;
  else_block.add(code_declt(clsid_tmp_sym.symbol_expr()));
  else_block.add(code_assignt(clsid_tmp_sym.symbol_expr(), object_clsid));

  exprt::operandst or_ops;
  for(const auto &clsname : children)
  {
    constant_exprt clsexpr(clsname, string_typet());
    equal_exprt test(clsid_tmp_sym.symbol_expr(), clsexpr);
    or_ops.push_back(test);
  }
  else_block.add(
    code_assignt(instanceof_result_sym.symbol_expr(), disjunction(or_ops)));

  const code_ifthenelset is_null_branch(
    equal_exprt(
      check_ptr, null_pointer_exprt(to_pointer_type(check_ptr.type()))),
    code_assignt(instanceof_result_sym.symbol_expr(), false_exprt()),
    std::move(else_block));

  // Replace the instanceof construct with instanceof_result:
  expr = instanceof_result_sym.symbol_expr();

  // Insert the new test block before it:
  goto_programt new_check_program;
  goto_convert(
    is_null_branch,
    symbol_table,
    new_check_program,
    message_handler,
    ID_java);

  goto_program.destructive_insert(this_inst, new_check_program);

  return true;
}

static bool contains_instanceof(const exprt &e)
{
  if(e.id() == ID_java_instanceof)
    return true;

  for(const exprt &subexpr : e.operands())
  {
    if(contains_instanceof(subexpr))
      return true;
  }

  return false;
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
  if(target->is_target() &&
     (contains_instanceof(target->code) || contains_instanceof(target->guard)))
  {
    // If this is a branch target, add a skip beforehand so we can splice new
    // GOTO programs before the target instruction without inserting into the
    // wrong basic block.
    goto_program.insert_before_swap(target);
    target->make_skip();
    // Actually alter the now-moved instruction:
    ++target;
  }

  return lower_instanceof(target->code, goto_program, target) |
    lower_instanceof(target->guard, goto_program, target);
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

/// Replace an instanceof in the expression or guard of the passed instruction
/// of the given function body with an explicit class-identifier test.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param target: The instruction to work on.
/// \param goto_program: The function body containing the instruction.
/// \param symbol_table: The symbol table to add symbols to.
/// \param class_hierarchy: class hierarchy analysis of symbol_table
/// \param message_handler: logging output
void remove_instanceof(
  goto_programt::targett target,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  message_handlert &message_handler)
{
  remove_instanceoft rem(symbol_table, class_hierarchy, message_handler);
  rem.lower_instanceof(goto_program, target);
}

/// Replace every instanceof in the passed function with an explicit
/// class-identifier test.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param function: The function to work on.
/// \param symbol_table: The symbol table to add symbols to.
/// \param class_hierarchy: class hierarchy analysis of symbol_table
/// \param message_handler: logging output
void remove_instanceof(
  goto_functionst::goto_functiont &function,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  message_handlert &message_handler)
{
  remove_instanceoft rem(symbol_table, class_hierarchy, message_handler);
  rem.lower_instanceof(function.body);
}

/// Replace every instanceof in every function with an explicit
/// class-identifier test.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param goto_functions: The functions to work on.
/// \param symbol_table: The symbol table to add symbols to.
/// \param class_hierarchy: class hierarchy analysis of symbol_table
/// \param message_handler: logging output
void remove_instanceof(
  goto_functionst &goto_functions,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  message_handlert &message_handler)
{
  remove_instanceoft rem(symbol_table, class_hierarchy, message_handler);
  bool changed=false;
  for(auto &f : goto_functions.function_map)
    changed=rem.lower_instanceof(f.second.body) || changed;
  if(changed)
    goto_functions.compute_location_numbers();
}

/// Replace every instanceof in every function with an explicit
/// class-identifier test.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param goto_model: The functions to work on and the symbol table to add
/// \param class_hierarchy: class hierarchy analysis of goto_model's symbol
///   table
/// \param message_handler: logging output
///   symbols to.
void remove_instanceof(
  goto_modelt &goto_model,
  const class_hierarchyt &class_hierarchy,
  message_handlert &message_handler)
{
  remove_instanceof(
    goto_model.goto_functions,
    goto_model.symbol_table,
    class_hierarchy,
    message_handler);
}
