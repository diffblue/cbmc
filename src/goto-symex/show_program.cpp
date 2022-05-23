/*******************************************************************\

Module: Output of the program (SSA) constraints

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Output of the program (SSA) constraints

#include "show_program.h"

#include <fstream>
#include <iostream>

#include <goto-symex/symex_target_equation.h>

#include <langapi/language_util.h>

#include <util/byte_operators.h>
#include <util/json_irep.h>
#include <util/ui_message.h>

/// Output a single SSA step
/// \param ns: Namespace
/// \param step: SSA step
/// \param annotation: Additonal information to include in step output
/// \param count: Step number, incremented after output
static void show_step(
  const namespacet &ns,
  const SSA_stept &step,
  const std::string &annotation,
  std::size_t &count)
{
  const irep_idt &function_id = step.source.function_id;

  std::string string_value = (step.is_shared_read() || step.is_shared_write())
                               ? from_expr(ns, function_id, step.ssa_lhs)
                               : from_expr(ns, function_id, step.cond_expr);
  if(step.ignore)
    std::cout << "(sliced) ";
  else
    std::cout << '(' << count << ") ";
  if(annotation.empty())
    std::cout << string_value;
  else
    std::cout << annotation << '(' << string_value << ')';
  std::cout << '\n';

  if(!step.guard.is_true())
  {
    const std::string guard_string = from_expr(ns, function_id, step.guard);
    std::cout << std::string(std::to_string(count).size() + 3, ' ');
    std::cout << "guard: " << guard_string << '\n';
  }

  ++count;
}

void show_program(const namespacet &ns, const symex_target_equationt &equation)
{
  std::size_t count = 1;

  std::cout << '\n' << "Program constraints:" << '\n';

  for(const auto &step : equation.SSA_steps)
  {
    std::cout << "// " << step.source.pc->location_number << " ";
    std::cout << step.source.pc->source_location().as_string() << "\n";

    if(step.is_assignment())
      show_step(ns, step, "", count);
    else if(step.is_assert())
      show_step(ns, step, "ASSERT", count);
    else if(step.is_assume())
      show_step(ns, step, "ASSUME", count);
    else if(step.is_constraint())
    {
      PRECONDITION(step.guard.is_true());
      show_step(ns, step, "CONSTRAINT", count);
    }
    else if(step.is_shared_read())
      show_step(ns, step, "SHARED_READ", count);
    else if(step.is_shared_write())
      show_step(ns, step, "SHARED_WRITE", count);
  }
}

template <typename expr_typet>
std::size_t count_expr_typed(const exprt &expr)
{
  static_assert(
    std::is_base_of<exprt, expr_typet>::value,
    "`expr_typet` is expected to be a type of `exprt`.");

  std::size_t count = 0;
  expr.visit_pre([&](const exprt &e) {
    if(can_cast_expr<expr_typet>(e))
      count++;
  });

  return count;
}

bool duplicated_previous_step(const SSA_stept &ssa_step)
{
  return !(
    ssa_step.is_assignment() || ssa_step.is_assert() || ssa_step.is_assume() ||
    ssa_step.is_constraint() || ssa_step.is_shared_read() ||
    ssa_step.is_shared_write());
}

void show_ssa_step_plain(
  messaget::mstreamt &out,
  const namespacet &ns,
  const SSA_stept &ssa_step,
  const exprt &ssa_expr)
{
  const irep_idt &function_id = ssa_step.source.function_id;
  const std::string ssa_expr_as_string = from_expr(ns, function_id, ssa_expr);

  out << messaget::faint << "// " << ssa_step.source.pc->location_number << " ";
  out << ssa_step.source.pc->source_location().as_string() << "\n"
      << messaget::reset;
  out << ssa_expr_as_string << "\n";
}

json_objectt get_ssa_step_json(
  const namespacet &ns,
  const SSA_stept &ssa_step,
  const exprt &ssa_expr)
{
  const std::string key_srcloc = "sourceLocation";
  const std::string key_ssa_expr = "ssaExpr";
  const std::string key_ssa_expr_as_string = "ssaExprString";

  const irep_idt &function_id = ssa_step.source.function_id;
  const std::string ssa_expr_as_string = from_expr(ns, function_id, ssa_expr);

  json_objectt json_ssa_step{
    {key_srcloc, json(ssa_step.source.pc->source_location())},
    {key_ssa_expr_as_string, json_stringt(ssa_expr_as_string)},
    {key_ssa_expr, json_irept(false).convert_from_irep(ssa_expr)}};

  return json_ssa_step;
}

template <typename expr_typet>
void show_byte_op_plain(
  messaget::mstreamt &out,
  const namespacet &ns,
  const symex_target_equationt &equation)
{
  std::size_t equation_byte_op_count = 0;
  for(const auto &step : equation.SSA_steps)
  {
    if(duplicated_previous_step(step))
      continue;

    const exprt &ssa_expr = step.get_ssa_expr();
    const std::size_t ssa_expr_byte_op_count =
      count_expr_typed<expr_typet>(ssa_expr);

    if(ssa_expr_byte_op_count == 0)
      continue;

    equation_byte_op_count += ssa_expr_byte_op_count;
    show_ssa_step_plain(out, ns, step, ssa_expr);
  }

  if(std::is_same<expr_typet, byte_extract_exprt>::value)
    out << '\n' << "Number of byte extracts: ";
  else if(std::is_same<expr_typet, byte_update_exprt>::value)
    out << '\n' << "Number of byte updates: ";
  else
    UNREACHABLE;

  out << equation_byte_op_count << '\n';
  out << messaget::eom;
}

template <typename expr_typet>
std::string json_get_key_byte_op_list()
{
  if(std::is_same<expr_typet, byte_extract_exprt>::value)
    return "byteExtractList";
  else if(std::is_same<expr_typet, byte_update_exprt>::value)
    return "byteUpdateList";
  else
    UNREACHABLE;
}

template <typename expr_typet>
std::string json_get_key_byte_op_num()
{
  if(std::is_same<expr_typet, byte_extract_exprt>::value)
    return "numOfExtracts";
  else if(std::is_same<expr_typet, byte_update_exprt>::value)
    return "numOfUpdates";
  else
    UNREACHABLE;
}

template <typename expr_typet>
json_objectt
get_byte_op_json(const namespacet &ns, const symex_target_equationt &equation)
{
  // Get key values to be used in the json output based on byte operation type
  // 1. json_get_key_byte_op_list():
  //    returns relevant json object key string where object records
  //    a list of expressions for given byte operation.
  // 2. json_get_key_byte_op_num():
  //    returns relevant json object key string where object number
  //    of given byte operation.

  const std::string key_byte_op_list = json_get_key_byte_op_list<expr_typet>();
  const std::string key_byte_op_num = json_get_key_byte_op_num<expr_typet>();

  json_objectt byte_op_stats;
  json_arrayt &byte_op_list = byte_op_stats[key_byte_op_list].make_array();

  std::size_t equation_byte_op_count = 0;
  for(const auto &step : equation.SSA_steps)
  {
    if(duplicated_previous_step(step))
      continue;

    const exprt &ssa_expr = step.get_ssa_expr();
    const std::size_t ssa_expr_byte_op_count =
      count_expr_typed<expr_typet>(ssa_expr);

    if(ssa_expr_byte_op_count == 0)
      continue;

    equation_byte_op_count += ssa_expr_byte_op_count;
    byte_op_list.push_back(get_ssa_step_json(ns, step, ssa_expr));
  }

  byte_op_stats[key_byte_op_num] =
    json_numbert(std::to_string(equation_byte_op_count));

  return byte_op_stats;
}

// Get key values to be used in the json output based on byte operation type
// 1. json_get_key_byte_op_stats():
//    returns relevant json object key string where object records
//    statistics for given byte operation.
template <typename expr_typet>
std::string json_get_key_byte_op_stats()
{
  if(std::is_same<expr_typet, byte_extract_exprt>::value)
    return "byteExtractStats";
  else if(std::is_same<expr_typet, byte_update_exprt>::value)
    return "byteUpdateStats";
  else
    UNREACHABLE;
}

bool is_outfile_specified(const optionst &options)
{
  const std::string &filename = options.get_option("outfile");
  return (!filename.empty() && filename != "-");
}

void show_byte_ops_plain(
  ui_message_handlert &ui_message_handler,
  std::ostream &out,
  bool outfile_given,
  const namespacet &ns,
  const symex_target_equationt &equation)
{
  messaget msg(ui_message_handler);
  if(outfile_given)
  {
    stream_message_handlert mout_handler(out);
    messaget mout(mout_handler);

    msg.status() << "\nByte Extracts written to file" << messaget::eom;
    show_byte_op_plain<byte_extract_exprt>(mout.status(), ns, equation);

    msg.status() << "\nByte Updates written to file" << messaget::eom;
    show_byte_op_plain<byte_update_exprt>(mout.status(), ns, equation);
  }
  else
  {
    msg.status() << "\nByte Extracts:" << messaget::eom;
    show_byte_op_plain<byte_extract_exprt>(msg.status(), ns, equation);

    msg.status() << "\nByte Updates:" << messaget::eom;
    show_byte_op_plain<byte_update_exprt>(msg.status(), ns, equation);
  }
}

void show_byte_ops_json(
  std::ostream &out,
  const namespacet &ns,
  const symex_target_equationt &equation)
{
  json_objectt byte_ops_stats{
    {json_get_key_byte_op_stats<byte_extract_exprt>(),
     get_byte_op_json<byte_extract_exprt>(ns, equation)},
    {json_get_key_byte_op_stats<byte_update_exprt>(),
     get_byte_op_json<byte_update_exprt>(ns, equation)}};

  json_objectt json_result;
  json_result["byteOpsStats"] = byte_ops_stats;

  out << ",\n" << json_result;
}

void show_byte_ops_xml(ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  msg.error()
    << "XML UI not supported for displaying byte extracts and updates."
    << " Try --json-ui instead" << messaget::eom;

  return;
}

void show_byte_ops(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  const namespacet &ns,
  const symex_target_equationt &equation)
{
  const std::string &filename = options.get_option("outfile");
  const bool outfile_given = is_outfile_specified(options);

  std::ofstream of;

  if(outfile_given)
  {
    of.open(filename, std::fstream::out);
    if(!of)
      throw invalid_command_line_argument_exceptiont(
        "failed to open output file: " + filename, "--outfile");
  }

  std::ostream &out = outfile_given ? of : std::cout;

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::XML_UI:
    show_byte_ops_xml(ui_message_handler);
    break;

  case ui_message_handlert::uit::JSON_UI:
    show_byte_ops_json(out, ns, equation);
    break;

  case ui_message_handlert::uit::PLAIN:
    show_byte_ops_plain(ui_message_handler, out, outfile_given, ns, equation);
    break;
  }
}
