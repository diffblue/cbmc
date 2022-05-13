/*******************************************************************\

Module: Local safe pointer analysis

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Local safe pointer analysis

#include "local_safe_pointers.h"

#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/symbol_table.h>

/// Return structure for `get_null_checked_expr` and
/// `get_conditional_checked_expr`
struct goto_null_checkt
{
  /// If true, the given GOTO/ASSUME tests that a pointer expression is non-null
  /// on the taken branch or passing case; otherwise, on the not-taken branch
  /// or on failure.
  bool checked_when_taken;

  /// Null-tested pointer expression
  exprt checked_expr;
};

/// Check if `expr` tests if a pointer is null
/// \param expr: expression to check
/// \return a `goto_null_checkt` indicating what expression is tested and
///   whether the check applies on the taken or not-taken branch, or an empty
///   optionalt if this isn't a null check.
static optionalt<goto_null_checkt> get_null_checked_expr(const exprt &expr)
{
  exprt normalized_expr = expr;
  // If true, then a null check is made when test `expr` passes; if false,
  // one is made when it fails.
  bool checked_when_taken = true;

  // Reduce some roundabout ways of saying "x != null", e.g. "!(x == null)".
  while(normalized_expr.id() == ID_not)
  {
    normalized_expr = to_not_expr(normalized_expr).op();
    checked_when_taken = !checked_when_taken;
  }

  if(normalized_expr.id() == ID_equal)
  {
    normalized_expr.id(ID_notequal);
    checked_when_taken = !checked_when_taken;
  }

  if(normalized_expr.id() == ID_notequal)
  {
    const exprt &op0 = skip_typecast(to_notequal_expr(normalized_expr).op0());
    const exprt &op1 = skip_typecast(to_notequal_expr(normalized_expr).op1());

    if(op0.type().id() == ID_pointer &&
       op0 == null_pointer_exprt(to_pointer_type(op0.type())))
    {
      return { { checked_when_taken, op1 } };
    }

    if(op1.type().id() == ID_pointer &&
       op1 == null_pointer_exprt(to_pointer_type(op1.type())))
    {
      return { { checked_when_taken, op0 } };
    }
  }

  return {};
}

/// Compute safe dereference expressions for a given GOTO program. This
/// populates `non_null_expressions` mapping instruction location numbers
/// onto a set of expressions that are known to be non-null BEFORE that
/// instruction is executed.
/// \param goto_program: program to analyse
void local_safe_pointerst::operator()(const goto_programt &goto_program)
{
  std::set<exprt, type_comparet> checked_expressions(type_comparet{});

  for(const auto &instruction : goto_program.instructions)
  {
    // Handle control-flow convergence pessimistically:
    if(instruction.incoming_edges.size() > 1)
      checked_expressions.clear();
    // Retrieve working set for forward GOTOs:
    else if(instruction.is_target())
    {
      auto findit = non_null_expressions.find(instruction.location_number);
      if(findit != non_null_expressions.end())
        checked_expressions = findit->second;
      else
      {
        checked_expressions = std::set<exprt, type_comparet>(type_comparet{});
      }
    }

    // Save the working set at this program point:
    if(!checked_expressions.empty())
    {
      non_null_expressions.emplace(
        instruction.location_number, checked_expressions);
    }

    switch(instruction.type())
    {
    // Instruction types that definitely don't write anything, and therefore
    // can't store a null pointer:
    case DECL:
    case DEAD:
    case ASSERT:
    case SKIP:
    case LOCATION:
    case SET_RETURN_VALUE:
    case THROW:
    case CATCH:
    case END_FUNCTION:
    case ATOMIC_BEGIN:
    case ATOMIC_END:
      break;

    // Possible checks:
    case ASSUME:
      if(auto assume_check = get_null_checked_expr(instruction.condition()))
      {
        if(assume_check->checked_when_taken)
          checked_expressions.insert(assume_check->checked_expr);
      }

      break;

    case GOTO:
      if(!instruction.is_backwards_goto())
      {
        // Copy current state to GOTO target:

        auto target_emplace_result =
          non_null_expressions.emplace(
            instruction.get_target()->location_number, checked_expressions);

        // If the target already has a state entry then it is a control-flow
        // merge point and everything will be assumed maybe-null in any case.
        if(target_emplace_result.second)
        {
          if(
            auto conditional_check =
              get_null_checked_expr(instruction.condition()))
          {
            // Add the GOTO condition to either the target or current state,
            // as appropriate:
            if(conditional_check->checked_when_taken)
            {
              target_emplace_result.first->second.insert(
                conditional_check->checked_expr);
            }
            else
              checked_expressions.insert(conditional_check->checked_expr);
          }
        }
      }

      break;

    case ASSIGN:
    case START_THREAD:
    case END_THREAD:
    case FUNCTION_CALL:
    case OTHER:
    case INCOMPLETE_GOTO:
    case NO_INSTRUCTION_TYPE:
      // Pessimistically assume all other instructions might overwrite any
      // pointer with a possibly-null value.
      checked_expressions.clear();
      break;
    }
  }
}

/// Output non-null expressions per instruction in human-readable format
/// \param out: stream to write output to
/// \param goto_program: GOTO program analysed (the same one passed to
///   operator())
/// \param ns: namespace
void local_safe_pointerst::output(
  std::ostream &out,
  const goto_programt &goto_program,
  const namespacet &ns)
{
  for(const auto &instruction : goto_program.instructions)
  {
    out << "**** " << instruction.location_number << " "
        << instruction.source_location() << "\n";

    out << "Non-null expressions: ";

    auto findit = non_null_expressions.find(instruction.location_number);
    if(findit == non_null_expressions.end())
      out << "{}";
    else
    {
      out << "{";
      bool first = true;
      for(const exprt &expr : findit->second)
      {
        if(!first)
          out << ", ";
        first = true;
        format_rec(out, expr);
      }
      out << "}";
    }

    out << '\n';
    goto_program.output_instruction(ns, irep_idt(), out, instruction);
    out << '\n';
  }
}

/// Output safely dereferenced expressions  per instruction in human-readable
///   format. For example, if we have an instruction `ASSUME x->y->z == a->b`
///   and we know expressions `x->y`, `a` and `other` are not null prior to it,
///   this will print `{x->y, a}`, the intersection of the `dereference_exprt`s
///   used here and the known-not-null expressions.
/// \param out: stream to write output to
/// \param goto_program: GOTO program analysed (the same one passed to
///   operator())
/// \param ns: namespace
void local_safe_pointerst::output_safe_dereferences(
  std::ostream &out,
  const goto_programt &goto_program,
  const namespacet &ns)
{
  for(const auto &instruction : goto_program.instructions)
  {
    out << "**** " << instruction.location_number << " "
        << instruction.source_location() << "\n";

    out << "Safe (known-not-null) dereferences: ";

    auto findit = non_null_expressions.find(instruction.location_number);
    if(findit == non_null_expressions.end())
      out << "{}";
    else
    {
      out << "{";
      bool first = true;
      instruction.apply([&first, &out](const exprt &e) {
        for(auto subexpr_it = e.depth_begin(), subexpr_end = e.depth_end();
            subexpr_it != subexpr_end;
            ++subexpr_it)
        {
          if(subexpr_it->id() == ID_dereference)
          {
            if(!first)
              out << ", ";
            first = true;
            format_rec(out, to_dereference_expr(*subexpr_it).pointer());
          }
        }
      });
      out << "}";
    }

    out << '\n';
    goto_program.output_instruction(ns, irep_idt(), out, instruction);
    out << '\n';
  }
}

/// Return true if the local-safe-pointers analysis has determined `expr` cannot
/// be null as of `program_point` (i.e. that `expr` is non-null when the
/// `program_point` instruction *starts* executing)
bool local_safe_pointerst::is_non_null_at_program_point(
  const exprt &expr, goto_programt::const_targett program_point)
{
  auto findit = non_null_expressions.find(program_point->location_number);
  if(findit == non_null_expressions.end())
    return false;

  return findit->second.count(skip_typecast(expr)) != 0;
}
