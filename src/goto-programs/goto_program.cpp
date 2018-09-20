/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_program.h"

#include <ostream>
#include <iomanip>

#include <util/std_expr.h>

#include <langapi/language_util.h>

/// Writes to \p out a two/three line string representation of a given
/// \p instruction. The output is of the format:
/// ```
///   // {location} file {source file} line {line in source file}
///   // Labels: {list-of-labels}
///   {representation of the instruction}
/// ```
/// \param ns: the namespace to resolve the expressions in
/// \param identifier: the identifier used to find a symbol to identify the
///   source language
/// \param out: the stream to write the goto string to
/// \param instruction: the instruction to convert
/// \return Appends to out a two line representation of the instruction
std::ostream &goto_programt::output_instruction(
  const namespacet &ns,
  const irep_idt &identifier,
  std::ostream &out,
  const instructiont &instruction) const
{
  out << "        // " << instruction.location_number << " ";

  if(!instruction.source_location.is_nil())
    out << instruction.source_location.as_string();
  else
    out << "no location";

  out << "\n";

  if(!instruction.labels.empty())
  {
    out << "        // Labels:";
    for(const auto &label : instruction.labels)
      out << " " << label;

    out << '\n';
  }

  if(instruction.is_target())
    out << std::setw(6) << instruction.target_number << ": ";
  else
    out << "        ";

  switch(instruction.type)
  {
  case NO_INSTRUCTION_TYPE:
    out << "NO INSTRUCTION TYPE SET" << '\n';
    break;

  case GOTO:
    if(!instruction.guard.is_true())
    {
      out << "IF "
          << from_expr(ns, identifier, instruction.guard)
          << " THEN ";
    }

    out << "GOTO ";

    for(instructiont::targetst::const_iterator
        gt_it=instruction.targets.begin();
        gt_it!=instruction.targets.end();
        gt_it++)
    {
      if(gt_it!=instruction.targets.begin())
        out << ", ";
      out << (*gt_it)->target_number;
    }

    out << '\n';
    break;

  case RETURN:
  case OTHER:
  case DECL:
  case DEAD:
  case FUNCTION_CALL:
  case ASSIGN:
    out << from_expr(ns, identifier, instruction.code) << '\n';
    break;

  case ASSUME:
  case ASSERT:
    if(instruction.is_assume())
      out << "ASSUME ";
    else
      out << "ASSERT ";

    {
      out << from_expr(ns, identifier, instruction.guard);

      const irep_idt &comment=instruction.source_location.get_comment();
      if(comment!="")
        out << " // " << comment;
    }

    out << '\n';
    break;

  case SKIP:
    out << "SKIP" << '\n';
    break;

  case END_FUNCTION:
    out << "END_FUNCTION" << '\n';
    break;

  case LOCATION:
    out << "LOCATION" << '\n';
    break;

  case THROW:
    out << "THROW";

    {
      const irept::subt &exception_list=
        instruction.code.find(ID_exception_list).get_sub();

      for(const auto &ex : exception_list)
        out << " " << ex.id();
    }

    if(instruction.code.operands().size()==1)
      out << ": " << from_expr(ns, identifier, instruction.code.op0());

    out << '\n';
    break;

  case CATCH:
  {
    if(instruction.code.get_statement()==ID_exception_landingpad)
    {
      const auto &landingpad=to_code_landingpad(instruction.code);
      out << "EXCEPTION LANDING PAD ("
          << from_type(ns, identifier, landingpad.catch_expr().type())
          << ' '
          << from_expr(ns, identifier, landingpad.catch_expr())
          << ")";
    }
    else if(instruction.code.get_statement()==ID_push_catch)
    {
      out << "CATCH-PUSH ";

      unsigned i=0;
      const irept::subt &exception_list=
        instruction.code.find(ID_exception_list).get_sub();
      DATA_INVARIANT(
        instruction.targets.size() == exception_list.size(),
        "unexpected discrepancy between sizes of instruction"
        "targets and exception list");
      for(instructiont::targetst::const_iterator
            gt_it=instruction.targets.begin();
          gt_it!=instruction.targets.end();
          gt_it++, i++)
      {
        if(gt_it!=instruction.targets.begin())
          out << ", ";
        out << exception_list[i].id() << "->"
            << (*gt_it)->target_number;
      }
    }
    else if(instruction.code.get_statement()==ID_pop_catch)
    {
      out << "CATCH-POP";
    }
    else
    {
      UNREACHABLE;
    }

    out << '\n';
    break;
  }

  case ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN" << '\n';
    break;

  case ATOMIC_END:
    out << "ATOMIC_END" << '\n';
    break;

  case START_THREAD:
    out << "START THREAD "
        << instruction.get_target()->target_number
        << '\n';
    break;

  case END_THREAD:
    out << "END THREAD" << '\n';
    break;

  default:
    UNREACHABLE;
  }

  return out;
}

void goto_programt::get_decl_identifiers(
  decl_identifierst &decl_identifiers) const
{
  forall_goto_program_instructions(it, (*this))
  {
    if(it->is_decl())
    {
      DATA_INVARIANT(
        it->code.get_statement() == ID_decl,
        "expected statement to be declaration statement");
      DATA_INVARIANT(
        it->code.operands().size() == 1,
        "declaration statement expects one operand");
      const symbol_exprt &symbol_expr=to_symbol_expr(it->code.op0());
      decl_identifiers.insert(symbol_expr.get_identifier());
    }
  }
}

void parse_lhs_read(const exprt &src, std::list<exprt> &dest)
{
  if(src.id()==ID_dereference)
  {
    dest.push_back(to_dereference_expr(src).pointer());
  }
  else if(src.id()==ID_index)
  {
    auto &index_expr = to_index_expr(src);
    dest.push_back(index_expr.index());
    parse_lhs_read(index_expr.array(), dest);
  }
  else if(src.id()==ID_member)
  {
    parse_lhs_read(to_member_expr(src).compound(), dest);
  }
  else if(src.id()==ID_if)
  {
    auto &if_expr = to_if_expr(src);
    dest.push_back(if_expr.cond());
    parse_lhs_read(if_expr.true_case(), dest);
    parse_lhs_read(if_expr.false_case(), dest);
  }
}

std::list<exprt> expressions_read(
  const goto_programt::instructiont &instruction)
{
  std::list<exprt> dest;

  switch(instruction.type)
  {
  case ASSUME:
  case ASSERT:
  case GOTO:
    dest.push_back(instruction.guard);
    break;

  case RETURN:
    if(to_code_return(instruction.code).return_value().is_not_nil())
      dest.push_back(to_code_return(instruction.code).return_value());
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &function_call=
        to_code_function_call(instruction.code);
      forall_expr(it, function_call.arguments())
        dest.push_back(*it);
      if(function_call.lhs().is_not_nil())
        parse_lhs_read(function_call.lhs(), dest);
    }
    break;

  case ASSIGN:
    {
      const code_assignt &assignment=to_code_assign(instruction.code);
      dest.push_back(assignment.rhs());
      parse_lhs_read(assignment.lhs(), dest);
    }
    break;

  default:
    {
    }
  }

  return dest;
}

std::list<exprt> expressions_written(
  const goto_programt::instructiont &instruction)
{
  std::list<exprt> dest;

  switch(instruction.type)
  {
  case FUNCTION_CALL:
    {
      const code_function_callt &function_call=
        to_code_function_call(instruction.code);
      if(function_call.lhs().is_not_nil())
        dest.push_back(function_call.lhs());
    }
    break;

  case ASSIGN:
    dest.push_back(to_code_assign(instruction.code).lhs());
    break;

  default:
    {
    }
  }

  return dest;
}

void objects_read(
  const exprt &src,
  std::list<exprt> &dest)
{
  if(src.id()==ID_symbol)
    dest.push_back(src);
  else if(src.id()==ID_address_of)
  {
    // don't traverse!
  }
  else if(src.id()==ID_dereference)
  {
    // this reads what is pointed to plus the pointer
    auto &deref = to_dereference_expr(src);
    dest.push_back(deref);
    objects_read(deref.pointer(), dest);
  }
  else
  {
    forall_operands(it, src)
      objects_read(*it, dest);
  }
}

std::list<exprt> objects_read(
  const goto_programt::instructiont &instruction)
{
  std::list<exprt> expressions=expressions_read(instruction);

  std::list<exprt> dest;

  for(const auto &expr : expressions)
    objects_read(expr, dest);

  return dest;
}

void objects_written(
  const exprt &src,
  std::list<exprt> &dest)
{
  if(src.id()==ID_if)
  {
    auto &if_expr = to_if_expr(src);
    objects_written(if_expr.true_case(), dest);
    objects_written(if_expr.false_case(), dest);
  }
  else
    dest.push_back(src);
}

std::list<exprt> objects_written(
  const goto_programt::instructiont &instruction)
{
  std::list<exprt> expressions=expressions_written(instruction);

  std::list<exprt> dest;

  for(const auto &expr : expressions)
    objects_written(expr, dest);

  return dest;
}

std::string as_string(
  const class namespacet &ns,
  const goto_programt::instructiont &i)
{
  std::string result;

  switch(i.type)
  {
  case NO_INSTRUCTION_TYPE:
    return "(NO INSTRUCTION TYPE)";

  case GOTO:
    if(!i.guard.is_true())
    {
      result+="IF "
            +from_expr(ns, i.function, i.guard)
            +" THEN ";
    }

    result+="GOTO ";

    for(goto_programt::instructiont::targetst::const_iterator
        gt_it=i.targets.begin();
        gt_it!=i.targets.end();
        gt_it++)
    {
      if(gt_it!=i.targets.begin())
        result+=", ";
      result+=std::to_string((*gt_it)->target_number);
    }
    return result;

  case RETURN:
  case OTHER:
  case DECL:
  case DEAD:
  case FUNCTION_CALL:
  case ASSIGN:
    return from_expr(ns, i.function, i.code);

  case ASSUME:
  case ASSERT:
    if(i.is_assume())
      result+="ASSUME ";
    else
      result+="ASSERT ";

    result+=from_expr(ns, i.function, i.guard);

    {
      const irep_idt &comment=i.source_location.get_comment();
      if(comment!="")
        result+=" /* "+id2string(comment)+" */";
    }
    return result;

  case SKIP:
    return "SKIP";

  case END_FUNCTION:
    return "END_FUNCTION";

  case LOCATION:
    return "LOCATION";

  case THROW:
    return "THROW";

  case CATCH:
    return "CATCH";

  case ATOMIC_BEGIN:
    return "ATOMIC_BEGIN";

  case ATOMIC_END:
    return "ATOMIC_END";

  case START_THREAD:
    result+="START THREAD ";

    if(i.targets.size()==1)
      result+=std::to_string(i.targets.front()->target_number);
    return result;

  case END_THREAD:
    return "END THREAD";

  default:
    UNREACHABLE;
  }
}

/// Assign each loop in the goto program a unique index. Every backwards goto is
/// considered a loop. The loops are numbered starting from zero and in the
/// order they appear in the goto program.
void goto_programt::compute_loop_numbers()
{
  unsigned nr=0;
  for(auto &i : instructions)
    if(i.is_backwards_goto())
      i.loop_number=nr++;
}

void goto_programt::update()
{
  compute_incoming_edges();
  compute_target_numbers();
  compute_location_numbers();
  compute_loop_numbers();
}

std::ostream &goto_programt::output(
  const namespacet &ns,
  const irep_idt &identifier,
  std::ostream &out) const
{
  // output program

  for(const auto &instruction : instructions)
    output_instruction(ns, identifier, out, instruction);

  return out;
}

/// Assign each target (i.e., an instruction that is in the `targets` list of
/// another instruction) a unique index.
///
/// Instructions that are not targets get target number instructiont::nil_target. The
/// targets are numbered starting from one and in the order they appear in the
/// goto program. An instruction is considered a target if it is the target of a
/// control-flow instruction (either GOTO or START_THREAD), i.e., it is
/// contained in the `targets` list of those instructions. Instructions that are
/// reached via straight-line control flow (fall-through for GOTO instructions)
/// only are not considered targets.
void goto_programt::compute_target_numbers()
{
  // reset marking

  for(auto &i : instructions)
    i.target_number=instructiont::nil_target;

  // mark the goto targets

  for(const auto &i : instructions)
  {
    for(const auto &t : i.targets)
    {
      if(t!=instructions.end())
        t->target_number=0;
    }
  }

  // number the targets properly
  unsigned cnt=0;

  for(auto &i : instructions)
  {
    if(i.is_target())
    {
      i.target_number=++cnt;
      DATA_INVARIANT(
        i.target_number != 0, "GOTO instruction target cannot be zero");
    }
  }

  // check the targets!
  // (this is a consistency check only)

  for(const auto &i : instructions)
  {
    for(const auto &t : i.targets)
    {
      if(t!=instructions.end())
      {
        DATA_INVARIANT(
          t->target_number != 0, "instruction's number cannot be zero");
        DATA_INVARIANT(
          t->target_number != instructiont::nil_target,
          "GOTO instruction target cannot be nil_target");
      }
    }
  }
}

/// Copy other goto program into this goto program. The current goto program is
/// cleared, and targets are adjusted as needed
///
/// \param src: the goto program to copy from
void goto_programt::copy_from(const goto_programt &src)
{
  // Definitions for mapping between the two programs
  typedef std::map<const_targett, targett> targets_mappingt;
  targets_mappingt targets_mapping;

  clear();

  // Loop over program - 1st time collects targets and copy

  for(instructionst::const_iterator
      it=src.instructions.begin();
      it!=src.instructions.end();
      ++it)
  {
    auto new_instruction=add_instruction();
    targets_mapping[it]=new_instruction;
    *new_instruction=*it;
  }

  // Loop over program - 2nd time updates targets

  for(auto &i : instructions)
  {
    for(auto &t : i.targets)
    {
      targets_mappingt::iterator
        m_target_it=targets_mapping.find(t);

      CHECK_RETURN(m_target_it != targets_mapping.end());

      t=m_target_it->second;
    }
  }

  compute_incoming_edges();
  compute_target_numbers();
}

/// Returns true if the goto program includes an `ASSERT` instruction the guard
/// of which is not trivially true.
bool goto_programt::has_assertion() const
{
  for(const auto &i : instructions)
    if(i.is_assert() && !i.guard.is_true())
      return true;

  return false;
}

/// Compute for each instruction the set of instructions it is a successor of.
void goto_programt::compute_incoming_edges()
{
  for(auto &i : instructions)
  {
    i.incoming_edges.clear();
  }

  for(instructionst::iterator
      it=instructions.begin();
      it!=instructions.end();
      ++it)
  {
    for(const auto &s : get_successors(it))
    {
      if(s!=instructions.end())
        s->incoming_edges.insert(it);
    }
  }
}

bool goto_programt::instructiont::equals(const instructiont &other) const
{
  // clang-format off
  return
    type == other.type &&
    code == other.code &&
    guard == other.guard &&
    targets.size() == other.targets.size() &&
    labels == other.labels;
  // clang-format on
}

bool goto_programt::equals(const goto_programt &other) const
{
  if(instructions.size() != other.instructions.size())
    return false;

  goto_programt::const_targett other_it = other.instructions.begin();
  for(const auto &ins : instructions)
  {
    if(!ins.equals(*other_it))
      return false;

    // the number of targets is the same as instructiont::equals returned "true"
    auto other_target_it = other_it->targets.begin();
    for(const auto t : ins.targets)
    {
      if(
        t->location_number - ins.location_number !=
        (*other_target_it)->location_number - other_it->location_number)
      {
        return false;
      }

      ++other_target_it;
    }

    ++other_it;
  }

  return true;
}
