/*******************************************************************\

Module: Show the goto functions as a dot program

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Show goto functions

#include "show_goto_proof_cfg.h"
#include "proof_cfg_metrics.h"

#include <util/ui_message.h>
#include <util/format_expr.h>
#include <math.h>

#include "goto_model.h"
#include "goto_program.h"
#include "pointer_expr.h"

bool is_private (const irep_idt &name) {
  // "__CPROVER_file_local_{filename}_c_{name}";

  const std::string str (name.c_str(), name.size());
  
  return (str.find ("__CPROVER_file_local_") != std::string::npos);
}

std::string normalize_name (const irep_idt &name) {
  // "__CPROVER_file_local_{filename}_c_{name}";

  const std::string str (name.c_str(), name.size());
  
  if (str.find ("__CPROVER_file_local_") != std::string::npos) {
    return str.substr (str.find ("_c_") + 3);

  }

  return str;
}

// the score metric associated with the function.
// a large score means the associated proof should be more difficult.
void compute_metrics (const symbolt &symbol, 
                      const goto_programt &goto_program, 
                      const namespacet &ns, 
                      const goto_functionst &goto_functions,
                      func_metrics &metrics) {
  metrics.indegree = indegree (symbol, ns, goto_functions);
  metrics.outdegree = outdegree (goto_program);
  metrics.num_func_pointer_calls = 0;
  metrics.function_size = function_size (goto_program);
  metrics.num_complex_ops = num_complex_ops (goto_program);
  metrics.num_loops = num_loops (goto_program);
}

void compute_metrics (const namespacet &ns, 
                     std::map<irep_idt, func_metrics> &metrics,
                     const goto_functionst &goto_functions) {
  const auto funs = goto_functions.sorted();

  for (const auto &fun : funs) {
    const symbolt &symbol = ns.lookup(fun->first);
    const irep_idt &name = symbol.name;
    const bool has_body = fun->second.body_available();
    if (has_body) {
      const goto_programt &body = fun->second.body;
      
      func_metrics &m = metrics.find(name)->second;
      compute_metrics (symbol, body, ns, goto_functions, m);
    }
  }
}

void compute_scores (std::map<irep_idt, func_metrics> &metrics,
                     std::map<irep_idt, int> &scores) {
  int w_indegree = 0;
  int w_outdegree = 0;
  int w_num_func_pointer_calls = 0;
  int w_function_size = 0;
  int w_num_complex_ops = 1;
  int w_num_loops = 1;

  for (auto it = metrics.begin(); it != metrics.end(); it++) {
    const irep_idt &name = it->first;
    const func_metrics &metrics = it->second;
    int score = metrics.indegree * w_indegree
              + metrics.outdegree * w_outdegree + 
              + metrics.num_func_pointer_calls * w_num_func_pointer_calls + 
              + metrics.function_size * w_function_size + 
              + metrics.num_complex_ops * w_num_complex_ops + 
              + metrics.num_loops * w_num_loops;
    scores.find(name)->second = score;
  }

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

bool is_used (const std::map<irep_idt, bool> &use, const irep_idt &name) {
    const auto used = use.find (name);
    return used != use.end() && used->second;
}

// simple depth first search
void find_used (irep_idt root,
                messaget &msg,
                const namespacet &ns,
                const goto_functionst &goto_functions,
                std::map<irep_idt, bool> &use) {
  if (use.find(root) == use.end()) {
    use.insert({root, true});
    const auto fun = goto_functions.function_map.find(root);
    if (fun != goto_functions.function_map.end()) {
      forall_goto_program_instructions(target, fun->second.body) {
        if(target->is_function_call()) {
          // only look at real function calls, not function pointer calls
          if (target->call_function().id() != ID_dereference) {
            const irep_idt call = ns.lookup(to_symbol_expr(target->call_function())).name;
            find_used (call, msg, ns, goto_functions, use);
          }
        }
      }
    }
  }
}

void remove_functions_no_body (const namespacet &ns,
                               const goto_functionst &goto_functions,
                               std::map<irep_idt, bool> &use) {
  const auto sorted = goto_functions.sorted();

  for(const auto &fun : sorted) {
    const symbolt &symbol = ns.lookup(fun->first);
    const bool has_body = fun->second.body_available();

    if (!has_body) {
      const auto find = use.find (symbol.name);
      if (find == use.end()) {
        use.insert ({symbol.name, false});
      } else {
        find->second = false;
      }
    }
  }
}

void show_goto_proof_cfg(
  const namespacet &ns,
  ui_message_handlert &ui_message_handler,
  const std::list<std::string> roots,
  const goto_functionst &goto_functions)
{

  //goto_functionst goto_functions;
  //goto_functions.copy_from(goto_functions_);

  messaget msg(ui_message_handler);

  std::map<irep_idt, bool> use;
   msg.status() << roots.size() << "\n";
  if (roots.size() == 0) {
    find_used (goto_functions.entry_point(), msg, ns, goto_functions, use);
  }
  for (const auto &root : roots) {
    const irep_idt &iden = root;
    find_used (iden, msg, ns, goto_functions, use);
    // msg.status() << iden << "\n";
  }

  remove_functions_no_body(ns, goto_functions, use);

  // sort functions alphabetically
  const auto sorted = goto_functions.sorted();

  msg.status() << "digraph G {\n\n";
  msg.status() << "rankdir=\"LR\";\n";

  std::map<irep_idt, int> scores;
  std::map<irep_idt, func_metrics> metrics;
  for (const auto &fun : sorted) {
    func_metrics m;
    m.indegree = 0;
    m.outdegree = 0;
    m.num_func_pointer_calls = 0;
    m.function_size = 0;
    m.num_complex_ops = 0;
    m.num_loops = 0;
    const auto &name = ns.lookup(fun->first).name;
    metrics.insert({name, m});
    scores.insert({name, 0});
  }
  // initialize scores
  compute_metrics (ns, metrics, goto_functions);
  compute_scores(metrics, scores);

  for(const auto &fun : sorted)
  {
    const symbolt &symbol = ns.lookup(fun->first);
    const bool has_body = fun->second.body_available();

    // msg.status() << "// " << symbol.name << " " << is_used (use, symbol.name) << "\n";

    if (is_used (use, symbol.name)) {

      if(has_body)
      {
        msg.status() << "// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\n";
        msg.status() << messaget::bold << "//" << symbol.display_name()
                     << messaget::reset << " /* " << symbol.name << " */\n";

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

        int node_size = (8 + sqrt(metrics.find(symbol.name)->second.function_size));
        std::string shape = is_private (symbol.name) ? "ellipse" : "rect";
        msg.status() << normalize_name (symbol.name)
                     << " [" 
                     << "shape=" << shape << ","
                     << "style=filled,"
                     << "fillcolor=" << "\"#" << color << "\","
          // << "fontsize=" << (8 + (255-s) / 16) 
                     << "fontsize=" << node_size
                     << "];\n";

        std::set<irep_idt> calls;
        std::set<std::string> func_ptrs;
        forall_goto_program_instructions(target, fun->second.body) {
          if(target->is_function_call()) {
            // overapproximate by adding duplicate calls
            const auto &func = target->call_function();

            // msg.status () << "//" << normalize_name (symbol.name) << target->source_location().get_comment() << "\n";
            msg.status () << "// " << normalize_name (symbol.name) 
                          << " " << target->source_location().as_string() << "\n";

            if (func.id() != ID_dereference) {
              const irep_idt call = ns.lookup(to_symbol_expr(func)).name;
              if (is_used (use, call)) {
                calls.insert (call);
              }

            } else {
              const exprt &pointer = to_dereference_expr(func).pointer();
              // TODO: idk what else it could be
              std::stringstream stream;
              stream << "\"" << format(pointer) << "\"";

              std::string rhs = stream.str();
              func_ptrs.insert (rhs);
              //if (pointer.id() == ID_symbol) {
              //  const irep_idt func_ptr = ns.lookup(to_symbol_expr(pointer)).name;
              //  func_ptrs.insert (func_ptr);
              //}
            }
          }
        }

        for (const auto &func_ptr : func_ptrs) {
          msg.status() << func_ptr
                       << " [" 
                       << "shape=" << "rarrow" << ","
                       << "style=filled,"
                       << "fillcolor=" << "\"#" << "ffffff" << "\","
                       << "fontsize=" << 8
                       << "];\n";
        }

        for (const auto &call : calls) {
          msg.status() << normalize_name(symbol.name) << " -> " << normalize_name(call) << ";\n";
        }

        for (const auto &func_ptr : func_ptrs) {
          msg.status() << normalize_name(symbol.name) << " -> " << func_ptr << ";\n";
        }

        // fun->second.body.output(ns, symbol.name, msg.status());
        // msg.status() << messaget::eom;
      }
      else
      {
        msg.status() << normalize_name (symbol.name)
                     << " [" 
                     << "shape=Mdiamond"
                     << "];\n";

      }
    }
  }

  // end digraph
  msg.status() << "}";
  msg.status() << messaget::eom;

}


void show_goto_proof_cfg(
  const goto_modelt &goto_model,
  const std::list<std::string> roots,
  ui_message_handlert &ui_message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  show_goto_proof_cfg(
    ns, ui_message_handler, roots, goto_model.goto_functions);
}
