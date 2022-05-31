/*******************************************************************\

Module: Show the goto functions as a dot program

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Show goto functions

#include "show_goto_proof_cfg.h"

#include <util/ui_message.h>
#include <util/format_expr.h>
#include <math.h>

#include "goto_model.h"
#include "goto_program.h"

int number_function_calls (const goto_programt::instructionst& instructions) {
  int count = 0;
  for (const auto &instruction : instructions) {
    switch (instruction.type())
    {
      // we may want to do something for GOTOs later
    case GOTO:
      break;
    case INCOMPLETE_GOTO:
      break;
    case FUNCTION_CALL:
      count = count + 1;

    case NO_INSTRUCTION_TYPE:
      break;
    case OTHER:
      break;
    case SET_RETURN_VALUE:
      break;
    case DECL:
      break;
    case DEAD:
      break;
    case ASSIGN:
      break;
    case ASSUME:
      break;
    case ASSERT:
      break;
    case SKIP:
      break;
    case END_FUNCTION:
      break;
    case LOCATION:
      break;
    case THROW:
      break;
    case CATCH:
      break;
    case ATOMIC_BEGIN:
      break;
    case ATOMIC_END:
      break;
    case START_THREAD:
      break;
    case END_THREAD:
      break;
    }

  }
  return count;
}

// the score metric associated with the function.
// a large score means the associated proof should be more difficult.
int score (const symbolt &symbol, const goto_programt::instructionst& instructions) {
  return number_function_calls (instructions);
}

void normalize_scores (std::map<irep_idt, int> &scores) {
  int max = 0;
  for (auto it = scores.begin(); it != scores.end(); it++) {
    max = std::max (max, it->second);
  }

  for (auto it = scores.begin(); it != scores.end(); it++) {
    // score between [0, inf)
    int score = it->second;
    // normalized score between [0, 255]
    float norm_score = 256.0 * ((float) score) / ((float) max);
    int normalized_score = std::min(255, std::max(0, (int) norm_score));
    it->second = normalized_score;
  }
  return;
}

void compute_scores (const namespacet &ns, 
                     std::map<irep_idt, int> &scores, 
                     const std::vector<goto_functionst::function_mapt::const_iterator> &funs) {
  for (const auto &fun : funs) {
    const symbolt &symbol = ns.lookup(fun->first);
    const irep_idt &name = symbol.name;
    int sc = 0;
    const bool has_body = fun->second.body_available();
    if (has_body) {
      const auto &instructions = fun->second.body.instructions;
      sc = score (symbol, instructions);
    }
    scores.insert ({name, sc});
  }
  normalize_scores(scores);
}

void show_goto_proof_cfg(
  const namespacet &ns,
  ui_message_handlert &ui_message_handler,
  const goto_functionst &goto_functions)
{
  messaget msg(ui_message_handler);
  
  // sort functions alphabetically
  const auto sorted = goto_functions.sorted();

  msg.status() << "digraph G {\n\n";

  std::map<irep_idt, int> scores;
  // initialize scores
  compute_scores (ns, scores, sorted);

  for(const auto &fun : sorted)
  {
    const symbolt &symbol = ns.lookup(fun->first);
    const bool has_body = fun->second.body_available();

    if(has_body)
    {
      msg.status() << "// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\n";
      msg.status() << messaget::bold << "//" << symbol.display_name()
                   << messaget::reset << " /* " << symbol.name << " */\n";

      const auto &instructions = fun->second.body.instructions;
      int s = scores.find (symbol.name)->second;
      // negate s so that higher original score => more red.
      s = 255 - s;

      std::stringstream stream;
      // Red
      stream << std::hex << 255;
      // Green
      if (s < 16) { stream << 0 << s; } else { stream << s; }
      // Blue
      if (s < 16) { stream << 0 << s; } else { stream << s; }
      std::string color( stream.str() );

      msg.status() << symbol.name 
                   << " [" 
                   << "style=filled,"
                   << "fillcolor=" << "\"#" << color << "\""
                   << "];\n";

      for (const auto &instruction : instructions) {
        switch (instruction.type())
        {
          // we may want to do something for GOTOs later
        case GOTO:
          break;
        case INCOMPLETE_GOTO:
          break;
        case FUNCTION_CALL:
          // overapproximate by adding duplicate calls
          msg.status() << symbol.name << " -> " << format(instruction.call_function()) << ";\n";

        case NO_INSTRUCTION_TYPE:
          break;
        case OTHER:
          break;
        case SET_RETURN_VALUE:
          break;
        case DECL:
          break;
        case DEAD:
          break;
        case ASSIGN:
          break;
        case ASSUME:
          break;
        case ASSERT:
          break;
        case SKIP:
          break;
        case END_FUNCTION:
          break;
        case LOCATION:
          break;
        case THROW:
          break;
        case CATCH:
          break;
        case ATOMIC_BEGIN:
          break;
        case ATOMIC_END:
          break;
        case START_THREAD:
          break;
        case END_THREAD:
          break;
        }

      }

      // fun->second.body.output(ns, symbol.name, msg.status());
      // msg.status() << messaget::eom;
    }
    else
    {
      msg.status() << symbol.name 
                   << " [" 
                   << "shape=Mdiamond"
                   << "];\n";

    }
  }

  // end digraph
  msg.status() << "}";
  msg.status() << messaget::eom;

}


void show_goto_proof_cfg(
  const goto_modelt &goto_model,
  ui_message_handlert &ui_message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  show_goto_proof_cfg(
    ns, ui_message_handler, goto_model.goto_functions);
}
