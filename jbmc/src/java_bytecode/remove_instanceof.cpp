/*******************************************************************\

Module: Remove Instance-of Operators

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Remove Instance-of Operators

#include "remove_instanceof.h"
#include "java_utils.h"

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/class_identifier.h>
#include <goto-programs/goto_convert.h>

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
  bool lower_instanceof(const irep_idt &function_identifier, goto_programt &);

  // Lower instanceof for a single instruction
  bool lower_instanceof(
    const irep_idt &function_identifier,
    goto_programt &,
    goto_programt::targett);

protected:
  symbol_table_baset &symbol_table;
  const class_hierarchyt &class_hierarchy;
  namespacet ns;
  message_handlert &message_handler;

  bool lower_instanceof(
    const irep_idt &function_identifier,
    exprt &,
    goto_programt &,
    goto_programt::targett);
};

/// Converts a classid into the classid of an n-dimensional array of that type.
/// Makes "java::array[reference(array[reference(A)])]" for example, for "A[][]"
/// \param underlying_type_name: classid of the innermost element type
/// \param array_dimensions: dimensionality of the array \p underlying_type_name
///   is contained within; can be zero for a non-array type.
/// \return array classid
static irep_idt add_array_qualifiers(
  const irep_idt &underlying_type_name,
  std::size_t array_dimensions)
{
  if(array_dimensions == 0)
    return underlying_type_name;

  std::ostringstream result;
  result << "java::";
  for(std::size_t i = 0; i < array_dimensions; ++i)
    result << "array[reference(";
  result << strip_java_namespace_prefix(underlying_type_name);
  for(std::size_t i = 0; i < array_dimensions; ++i)
    result << ")]";
  return result.str();
}

/// Replaces an expression like e instanceof A with e.\@class_identifier == "A"
/// or a big-or of similar expressions if we know of subtypes that also satisfy
/// the given test.
/// \param function_identifier: name of the goto function \p goto_program
/// \param expr: Expression to lower (the code or the guard of an instruction)
/// \param goto_program: program the expression belongs to
/// \param this_inst: instruction the expression is found at
/// \return true if any instanceof instructionw was replaced
bool remove_instanceoft::lower_instanceof(
  const irep_idt &function_identifier,
  exprt &expr,
  goto_programt &goto_program,
  goto_programt::targett this_inst)
{
  if(expr.id()!=ID_java_instanceof)
  {
    bool changed = false;
    Forall_operands(it, expr)
      changed |=
        lower_instanceof(function_identifier, *it, goto_program, this_inst);
    return changed;
  }

  INVARIANT(
    expr.operands().size()==2,
    "java_instanceof should have two operands");

  const exprt &check_ptr = to_binary_expr(expr).op0();
  INVARIANT(
    check_ptr.type().id()==ID_pointer,
    "instanceof first operand should be a pointer");

  const exprt &target_arg = to_binary_expr(expr).op1();
  INVARIANT(
    target_arg.id()==ID_type,
    "instanceof second operand should be a type");
  const typet &target_type=target_arg.type();

  // Find all types we know about that satisfy the given requirement:
  INVARIANT(
    target_type.id() == ID_struct_tag,
    "instanceof second operand should have a simple type");

  if(
    to_struct_tag_type(target_type).get_identifier() ==
    "java::java.lang.Object")
  {
    // Everything derives from Object, and special-casing this particular check
    // means we don't need to check all array dimensionalities, which also
    // derive from Object, but finding the highest-dimensioned array in the
    // program under test is not trivial.
    expr = true_exprt();
    return true;
  }

  // If checking for an array type, the target type must have the same
  // dimension:
  const auto underlying_type_and_dimension =
    java_array_dimension_and_element_type(to_struct_tag_type(target_type));

  const irep_idt &underlying_name =
    underlying_type_and_dimension.first.get_identifier();
  std::vector<irep_idt> children =
    class_hierarchy.get_children_trans(underlying_name);
  children.push_back(underlying_name);
  // Sort alphabetically to make order of generated disjuncts
  // independent of class loading order
  std::sort(
    children.begin(), children.end(), [](const irep_idt &a, const irep_idt &b) {
      return a.compare(b) < 0;
    });

  auto jlo = to_struct_tag_type(java_lang_object_type().subtype());
  exprt object_clsid = get_class_identifier_field(check_ptr, jlo, ns);

  // Replace the instanceof operation with (check_ptr != null &&
  //  (check_ptr->@class_identifier == "A" ||
  //   check_ptr->@class_identifier == "B" || ...

  // By operating directly on a pointer rather than using a temporary
  // (x->@clsid == "A" rather than id = x->@clsid; id == "A") we enable symex's
  // value-set filtering to discard no-longer-viable candidates for "x" (in the
  // case where 'x' is a symbol, not a general expression like x->y->@clsid).
  // This means there are more clean dereference operations (ones where there
  // is no possibility of reading a null, invalid or incorrectly-typed object),
  // and less pessimistic aliasing assumptions possibly causing goto-symex to
  // explore in-fact-unreachable paths.

  exprt::operandst or_ops;
  for(const auto &clsname : children)
  {
    irep_idt full_type_name =
      add_array_qualifiers(clsname, underlying_type_and_dimension.second);
    constant_exprt clsexpr(full_type_name, string_typet());
    equal_exprt test(object_clsid, clsexpr);
    or_ops.push_back(test);
  }

  notequal_exprt not_null(
    check_ptr, null_pointer_exprt(to_pointer_type(check_ptr.type())));

  expr = and_exprt(not_null, disjunction(or_ops));

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
/// \param function_identifier: name of the goto function \p goto_program
/// \param goto_program: program to process
/// \param target: instruction to check for instanceof expressions
/// \return true if an instanceof has been replaced
bool remove_instanceoft::lower_instanceof(
  const irep_idt &function_identifier,
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
    target->turn_into_skip();
    // Actually alter the now-moved instruction:
    ++target;
  }

  return lower_instanceof(
           function_identifier, target->code, goto_program, target) |
         lower_instanceof(
           function_identifier, target->guard, goto_program, target);
}

/// Replace every instanceof in the passed function body with an explicit
/// class-identifier test.
/// Extra auxiliary variables may be introduced into symbol_table.
/// \param function_identifier: name of the goto function \p goto_program
/// \param goto_program: The function body to work on.
/// \return true if one or more instanceof expressions have been replaced
bool remove_instanceoft::lower_instanceof(
  const irep_idt &function_identifier,
  goto_programt &goto_program)
{
  bool changed=false;
  for(goto_programt::instructionst::iterator target=
      goto_program.instructions.begin();
    target!=goto_program.instructions.end();
    ++target)
  {
    changed =
      lower_instanceof(function_identifier, goto_program, target) || changed;
  }
  if(!changed)
    return false;
  goto_program.update();
  return true;
}

/// Replace an instanceof in the expression or guard of the passed instruction
/// of the given function body with an explicit class-identifier test.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param function_identifier: name of the goto function \p goto_program
/// \param target: The instruction to work on.
/// \param goto_program: The function body containing the instruction.
/// \param symbol_table: The symbol table to add symbols to.
/// \param class_hierarchy: class hierarchy analysis of symbol_table
/// \param message_handler: logging output
void remove_instanceof(
  const irep_idt &function_identifier,
  goto_programt::targett target,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  message_handlert &message_handler)
{
  remove_instanceoft rem(symbol_table, class_hierarchy, message_handler);
  rem.lower_instanceof(function_identifier, goto_program, target);
}

/// Replace every instanceof in the passed function with an explicit
/// class-identifier test.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param function_identifier: name of the goto function \p function
/// \param function: The function to work on.
/// \param symbol_table: The symbol table to add symbols to.
/// \param class_hierarchy: class hierarchy analysis of symbol_table
/// \param message_handler: logging output
void remove_instanceof(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &function,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  message_handlert &message_handler)
{
  remove_instanceoft rem(symbol_table, class_hierarchy, message_handler);
  rem.lower_instanceof(function_identifier, function.body);
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
    changed = rem.lower_instanceof(f.first, f.second.body) || changed;
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
