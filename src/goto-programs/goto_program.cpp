/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_program.h"

#include <ostream>
#include <iomanip>

#include <util/base_type.h>
#include <util/expr_iterator.h>
#include <util/find_symbols.h>
#include <util/invariant.h>
#include <util/std_expr.h>
#include <util/validate.h>

#include <langapi/language_util.h>

#include "remove_returns.h"

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
  case INCOMPLETE_GOTO:
    if(!instruction.get_condition().is_true())
    {
      out << "IF " << from_expr(ns, identifier, instruction.get_condition())
          << " THEN ";
    }

    out << "GOTO ";

    if(instruction.is_incomplete_goto())
    {
      out << "(incomplete)";
    }
    else
    {
      for(auto gt_it = instruction.targets.begin();
          gt_it != instruction.targets.end();
          gt_it++)
      {
        if(gt_it != instruction.targets.begin())
          out << ", ";
        out << (*gt_it)->target_number;
      }
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
      out << from_expr(ns, identifier, instruction.get_condition());

      const irep_idt &comment=instruction.source_location.get_comment();
      if(!comment.empty())
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
    dest.push_back(instruction.get_condition());
    break;

  case RETURN:
    if(instruction.get_return().return_value().is_not_nil())
      dest.push_back(instruction.get_return().return_value());
    break;

  case FUNCTION_CALL:
  {
    const code_function_callt &function_call = instruction.get_function_call();
    forall_expr(it, function_call.arguments())
      dest.push_back(*it);
    if(function_call.lhs().is_not_nil())
      parse_lhs_read(function_call.lhs(), dest);
    break;
  }

  case ASSIGN:
  {
    const code_assignt &assignment = instruction.get_assign();
    dest.push_back(assignment.rhs());
    parse_lhs_read(assignment.lhs(), dest);
    break;
  }

  case CATCH:
  case THROW:
  case DEAD:
  case DECL:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case START_THREAD:
  case END_THREAD:
  case END_FUNCTION:
  case LOCATION:
  case SKIP:
  case OTHER:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    break;
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
      const code_function_callt &function_call =
        instruction.get_function_call();
      if(function_call.lhs().is_not_nil())
        dest.push_back(function_call.lhs());
    }
    break;

  case ASSIGN:
    dest.push_back(instruction.get_assign().lhs());
    break;

  case CATCH:
  case THROW:
  case GOTO:
  case RETURN:
  case DEAD:
  case DECL:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case START_THREAD:
  case END_THREAD:
  case END_FUNCTION:
  case ASSERT:
  case ASSUME:
  case LOCATION:
  case SKIP:
  case OTHER:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    break;
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
  const irep_idt &function,
  const goto_programt::instructiont &i)
{
  std::string result;

  switch(i.type)
  {
  case NO_INSTRUCTION_TYPE:
    return "(NO INSTRUCTION TYPE)";

  case GOTO:
    if(!i.get_condition().is_true())
    {
      result += "IF " + from_expr(ns, function, i.get_condition()) + " THEN ";
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
    return from_expr(ns, function, i.code);

  case ASSUME:
  case ASSERT:
    if(i.is_assume())
      result+="ASSUME ";
    else
      result+="ASSERT ";

    result += from_expr(ns, function, i.get_condition());

    {
      const irep_idt &comment=i.source_location.get_comment();
      if(!comment.empty())
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

  case INCOMPLETE_GOTO:
    UNREACHABLE;
  }

  UNREACHABLE;
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
    if(i.is_assert() && !i.get_condition().is_true())
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

void goto_programt::instructiont::validate(
  const namespacet &ns,
  const validation_modet vm) const
{
  validate_full_code(code, ns, vm);
  validate_full_expr(guard, ns, vm);

  auto expr_symbol_finder = [&](const exprt &e) {
    find_symbols_sett typetags;
    find_type_symbols(e.type(), typetags);
    find_symbols_or_nexts(e, typetags);
    const symbolt *symbol;
    for(const auto &identifier : typetags)
    {
      DATA_CHECK_WITH_DIAGNOSTICS(
        vm,
        !ns.lookup(identifier, symbol),
        id2string(identifier) + " not found",
        source_location);
    }
  };

  auto &current_source_location = source_location;
  auto type_finder =
    [&ns, vm, &current_source_location](const exprt &e) {
      if(e.id() == ID_symbol)
      {
        const auto &goto_symbol_expr = to_symbol_expr(e);
        const auto &goto_id = goto_symbol_expr.get_identifier();

        const symbolt *table_symbol;
        if(!ns.lookup(goto_id, table_symbol))
        {
          bool symbol_expr_type_matches_symbol_table =
            base_type_eq(goto_symbol_expr.type(), table_symbol->type, ns);

          if(
            !symbol_expr_type_matches_symbol_table &&
            table_symbol->type.id() == ID_code)
          {
            // If a function declaration and its definition are in different
            // translation units they may have different return types.
            // Thus, the return type in the symbol table may differ
            // from the return type in the symbol expr.
            if(
              goto_symbol_expr.type().source_location().get_file() !=
              table_symbol->type.source_location().get_file())
            {
              // temporarily fixup the return types
              auto goto_symbol_expr_type =
                to_code_type(goto_symbol_expr.type());
              auto table_symbol_type = to_code_type(table_symbol->type);

              goto_symbol_expr_type.return_type() =
                table_symbol_type.return_type();

              symbol_expr_type_matches_symbol_table =
                base_type_eq(goto_symbol_expr_type, table_symbol_type, ns);
            }
          }

          if(
            !symbol_expr_type_matches_symbol_table &&
            goto_symbol_expr.type().id() == ID_array &&
            to_array_type(goto_symbol_expr.type()).is_incomplete())
          {
            // If the symbol expr has an incomplete array type, it may not have
            // a constant size value, whereas the symbol table entry may have
            // an (assumed) constant size of 1 (which mimics gcc behaviour)
            if(table_symbol->type.id() == ID_array)
            {
              auto symbol_table_array_type = to_array_type(table_symbol->type);
              symbol_table_array_type.size() = nil_exprt();

              symbol_expr_type_matches_symbol_table =
                goto_symbol_expr.type() == symbol_table_array_type;
            }
          }

          DATA_CHECK_WITH_DIAGNOSTICS(
            vm,
            symbol_expr_type_matches_symbol_table,
            id2string(goto_id) + " type inconsistency\n" +
              "goto program type: " + goto_symbol_expr.type().id_string() +
              "\n" + "symbol table type: " + table_symbol->type.id_string(),
            current_source_location);
        }
      }
    };

  const symbolt *table_symbol;
  switch(type)
  {
  case NO_INSTRUCTION_TYPE:
    break;
  case GOTO:
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      has_target(),
      "goto instruction expects at least one target",
      source_location);
    // get_target checks that targets.size()==1
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      get_target()->is_target() && get_target()->target_number != 0,
      "goto target has to be a target",
      source_location);
    break;
  case ASSUME:
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      targets.empty(),
      "assume instruction should not have a target",
      source_location);
    break;
  case ASSERT:
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      targets.empty(),
      "assert instruction should not have a target",
      source_location);

    std::for_each(guard.depth_begin(), guard.depth_end(), expr_symbol_finder);
    std::for_each(guard.depth_begin(), guard.depth_end(), type_finder);
    break;
  case OTHER:
    break;
  case SKIP:
    break;
  case START_THREAD:
    break;
  case END_THREAD:
    break;
  case LOCATION:
    break;
  case END_FUNCTION:
    break;
  case ATOMIC_BEGIN:
    break;
  case ATOMIC_END:
    break;
  case RETURN:
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      code.get_statement() == ID_return,
      "return instruction should contain a return statement",
      source_location);
    break;
  case ASSIGN:
    DATA_CHECK(
      vm,
      code.get_statement() == ID_assign,
      "assign instruction should contain an assign statement");
    DATA_CHECK(
      vm, targets.empty(), "assign instruction should not have a target");
    break;
  case DECL:
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      code.get_statement() == ID_decl,
      "declaration instructions should contain a declaration statement",
      source_location);
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      !ns.lookup(get_decl().get_identifier(), table_symbol),
      "declared symbols should be known",
      id2string(get_decl().get_identifier()),
      source_location);
    break;
  case DEAD:
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      code.get_statement() == ID_dead,
      "dead instructions should contain a dead statement",
      source_location);
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      !ns.lookup(get_dead().get_identifier(), table_symbol),
      "removed symbols should be known",
      id2string(get_dead().get_identifier()),
      source_location);
    break;
  case FUNCTION_CALL:
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      code.get_statement() == ID_function_call,
      "function call instruction should contain a call statement",
      source_location);

    std::for_each(code.depth_begin(), code.depth_end(), expr_symbol_finder);
    std::for_each(code.depth_begin(), code.depth_end(), type_finder);
    break;
  case THROW:
    break;
  case CATCH:
    break;
  case INCOMPLETE_GOTO:
    break;
  }
}

void goto_programt::instructiont::transform(
  std::function<optionalt<exprt>(exprt)> f)
{
  switch(type)
  {
  case OTHER:
    if(get_other().get_statement() == ID_expression)
    {
      auto new_expression = f(to_code_expression(get_other()).expression());
      if(new_expression.has_value())
      {
        auto new_other = to_code_expression(get_other());
        new_other.expression() = *new_expression;
        set_other(new_other);
      }
    }
    break;

  case RETURN:
  {
    auto new_return_value = f(get_return().return_value());
    if(new_return_value.has_value())
    {
      auto new_return = get_return();
      new_return.return_value() = *new_return_value;
      set_return(new_return);
    }
  }
  break;

  case ASSIGN:
  {
    auto new_assign_lhs = f(get_assign().lhs());
    auto new_assign_rhs = f(get_assign().rhs());
    if(new_assign_lhs.has_value() || new_assign_rhs.has_value())
    {
      auto new_assignment = get_assign();
      new_assignment.lhs() = new_assign_lhs.value_or(new_assignment.lhs());
      new_assignment.rhs() = new_assign_rhs.value_or(new_assignment.rhs());
      set_assign(new_assignment);
    }
  }
  break;

  case DECL:
  {
    auto new_symbol = f(get_decl().symbol());
    if(new_symbol.has_value())
    {
      auto new_decl = get_decl();
      new_decl.symbol() = to_symbol_expr(*new_symbol);
      set_decl(new_decl);
    }
  }
  break;

  case DEAD:
  {
    auto new_symbol = f(get_dead().symbol());
    if(new_symbol.has_value())
    {
      auto new_dead = get_dead();
      new_dead.symbol() = to_symbol_expr(*new_symbol);
      set_dead(new_dead);
    }
  }
  break;

  case FUNCTION_CALL:
  {
    auto new_call = get_function_call();
    bool change = false;

    auto new_lhs = f(new_call.lhs());
    if(new_lhs.has_value())
    {
      new_call.lhs() = *new_lhs;
      change = true;
    }

    for(auto &a : new_call.arguments())
    {
      auto new_a = f(a);
      if(new_a.has_value())
      {
        a = *new_a;
        change = true;
      }
    }

    if(change)
      set_function_call(new_call);
  }
  break;

  case GOTO:
  case ASSUME:
  case ASSERT:
  case SKIP:
  case START_THREAD:
  case END_THREAD:
  case LOCATION:
  case END_FUNCTION:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case THROW:
  case CATCH:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    if(has_condition())
    {
      auto new_condition = f(get_condition());
      if(new_condition.has_value())
        set_condition(new_condition.value());
    }
  }
}

void goto_programt::instructiont::apply(
  std::function<void(const exprt &)> f) const
{
  switch(type)
  {
  case OTHER:
    if(get_other().get_statement() == ID_expression)
      f(to_code_expression(get_other()).expression());
    break;

  case RETURN:
    f(get_return().return_value());
    break;

  case ASSIGN:
    f(get_assign().lhs());
    f(get_assign().rhs());
    break;

  case DECL:
    f(get_decl().symbol());
    break;

  case DEAD:
    f(get_dead().symbol());
    break;

  case FUNCTION_CALL:
  {
    const auto &call = get_function_call();
    f(call.lhs());
    for(auto &a : call.arguments())
      f(a);
  }
  break;

  case GOTO:
  case ASSUME:
  case ASSERT:
  case SKIP:
  case START_THREAD:
  case END_THREAD:
  case LOCATION:
  case END_FUNCTION:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case THROW:
  case CATCH:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    if(has_condition())
      f(get_condition());
  }
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

/// Outputs a string representation of a `goto_program_instruction_typet`
std::ostream &operator<<(std::ostream &out, goto_program_instruction_typet t)
{
  switch(t)
  {
  case NO_INSTRUCTION_TYPE:
    out << "NO_INSTRUCTION_TYPE";
    break;
  case GOTO:
    out << "GOTO";
    break;
  case ASSUME:
    out << "ASSUME";
    break;
  case ASSERT:
    out << "ASSERT";
    break;
  case OTHER:
    out << "OTHER";
    break;
  case DECL:
    out << "DECL";
    break;
  case DEAD:
    out << "DEAD";
    break;
  case SKIP:
    out << "SKIP";
    break;
  case START_THREAD:
    out << "START_THREAD";
    break;
  case END_THREAD:
    out << "END_THREAD";
    break;
  case LOCATION:
    out << "LOCATION";
    break;
  case END_FUNCTION:
    out << "END_FUNCTION";
    break;
  case ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN";
    break;
  case ATOMIC_END:
    out << "ATOMIC_END";
    break;
  case RETURN:
    out << "RETURN";
    break;
  case ASSIGN:
    out << "ASSIGN";
    break;
  case FUNCTION_CALL:
    out << "FUNCTION_CALL";
    break;
  case THROW:
    out << "THROW";
    break;
  case CATCH:
    out << "CATCH";
    break;
  case INCOMPLETE_GOTO:
    out << "INCOMPLETE_GOTO";
    break;
  }

  return out;
}
