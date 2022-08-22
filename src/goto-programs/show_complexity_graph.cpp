/*******************************************************************\

Module: Show the goto functions as a dot program

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Show goto functions

#include "show_complexity_graph.h"

#include <iostream>
#include <iomanip>
#include <fstream>
#include <math.h>

#include <util/ui_message.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/std_code.h>

#include "goto_model.h"
#include "pointer_expr.h"
#include "complexity_graph.h"

#include <goto-checker/symex_coverage.h>

#include "compute_called_functions.h"
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_const_function_pointers.h>

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

void function_pointer_setup (const symbol_tablet &symbol_table,
                             const namespacet &ns,
                             const goto_functionst &goto_functions,
                             std::map<irep_idt, code_typet> &type_map,
                             std::unordered_set<irep_idt> &address_taken) {

  for(const auto &s : symbol_table.symbols) {
    compute_address_taken_functions(s.second.value, address_taken);
  }

  compute_address_taken_functions(goto_functions, address_taken);

  for(const auto &gf_entry : goto_functions.function_map)
  {
    type_map.emplace(
      gf_entry.first, to_code_type(ns.lookup(gf_entry.first).type));
  }

}

void find_functions_for_function_pointer (const symbol_tablet &symbol_table,
                                          const namespacet &ns,
                                          remove_const_function_pointerst::functionst &functions,
                                          message_handlert &message_handler,
                                          const goto_programt::const_targett &target,
                                          const std::map<irep_idt, code_typet> &type_map,
                                          const std::unordered_set<irep_idt> &address_taken) {

  const auto &function = to_dereference_expr(as_const(*target).call_function());

  // this better have the right type
  code_typet call_type=to_code_type(function.type());

  // refine the type in case the forward declaration was incomplete
  if(call_type.has_ellipsis() &&
     call_type.parameters().empty())
  {
    call_type.remove_ellipsis();
    for(const auto &argument : as_const(*target).call_arguments())
    {
      call_type.parameters().push_back(code_typet::parametert(argument.type()));
    }
  }

  const exprt &pointer = function.pointer();
  remove_const_function_pointerst fpr(message_handler, ns, symbol_table);
  bool found_functions=fpr(pointer, functions);

  if(!found_functions)
  {
    bool return_value_used = as_const(*target).call_lhs().is_not_nil();

    // get all type-compatible functions
    // whose address is ever taken
    for(const auto &t : type_map)
    {
      // address taken?
      if(address_taken.find(t.first)==address_taken.end())
        continue;

      // type-compatible?
      if(!function_is_type_compatible(
           return_value_used, call_type, t.second, ns))
        continue;

      if(t.first=="pthread_mutex_cleanup")
        continue;

      symbol_exprt expr(t.first, t.second);
      functions.insert(expr);
    }
  }

}

void produce_node_rec (const goto_functionst &goto_functions,
                       const namespacet &ns,
                       const irep_idt name, 
                       complexity_grapht &graph,
                       const std::set<irep_idt> &omitted_functions,
                       const bool omit_function_pointers, 
                       std::function<void(goto_programt::const_targett&, remove_const_function_pointerst::functionst&)> find_functions_for_function_pointer) {

  if (!(graph.has_node (name))) {

    std::string display_name = normalize_name(name);
    complexity_grapht::nodet &node = graph.add_node (complexity_grapht::nodet (name, display_name, complexity_grapht::nodet::node_typet::FUNCTION));

    if (is_private(name)) {
      node.add_property ("private");
    }

    const auto fun = goto_functions.function_map.find(name);
    if (fun != goto_functions.function_map.end()) {
      bool has_body = fun->second.body_available();

      if (has_body) {
        auto target = fun->second.body.instructions.begin();
        auto end = fun->second.body.instructions.end();

        while (target != end) {

          // FUTURE: can segment function bodies into loops

          std::vector<goto_programt::const_targett> initial;
          node.instructions.push_back(initial);
          node.instructions[0].push_back (target);

          if(target->is_function_call()) {
            if (target->call_function().id() != ID_dereference) {

              const irep_idt call = ns.lookup(to_symbol_expr(target->call_function())).name;

              std::stringstream stream;
              stream << call;
              std::string str_call = stream.str();
        
              if (omitted_functions.find(str_call) == omitted_functions.end()) {
                if (!graph.has_node(call)) {
                  produce_node_rec (goto_functions, ns, call, graph,
                                    omitted_functions,
                                    omit_function_pointers, find_functions_for_function_pointer);
                }
                graph.add_edge (node.name, call);
              }
            } else {
              if (!omit_function_pointers) {
                const exprt &pointer = to_dereference_expr(target->call_function()).pointer();
                std::stringstream stream;
                stream << "\"" << format(pointer) << "\"";

        
                std::stringstream rhs_stream;
                rhs_stream << node.name << "." << stream.str();
                std::string rhs = rhs_stream.str();
                std::string rhs_display = stream.str();
        
                graph.add_node (complexity_grapht::nodet (rhs, rhs_display, complexity_grapht::nodet::node_typet::FUNCTION_POINTER));
                graph.add_edge (node.name, rhs);

                remove_const_function_pointerst::functionst functions;

                find_functions_for_function_pointer (target, functions);
                for (const symbol_exprt &function : functions) {
                  const irep_idt &name = function.get_identifier();
                  if (!graph.has_node (name)) {
                    graph.add_node (complexity_grapht::nodet (name, normalize_name (name), complexity_grapht::nodet::node_typet::FUNCTION));
                  }

                  graph.add_edge (rhs, name);
                }
              }
            }
          }

          target++;
        }

        
      } else {
        node.add_property ("no_body");
      }
    } else {
      node.add_property ("no_definition");
    }
  }
}

void produce_graph (
  const symbol_tablet &symbol_table,
  const namespacet &ns,
  message_handlert& message_handler,
  const std::map<irep_idt, code_typet> &type_map,
  const std::unordered_set<irep_idt> &address_taken,
  const std::vector<irep_idt> &roots,
  const goto_functionst &goto_functions,
  complexity_grapht &graph,
  const bool omit_function_pointers,
  const std::set<irep_idt> &omitted_functions
  ) {

  std::function<void(goto_programt::const_targett&, remove_const_function_pointerst::functionst&)> find_functions_for_fp = 
    [&symbol_table, &ns, &message_handler, &type_map, &address_taken] (goto_programt::const_targett &target, remove_const_function_pointerst::functionst &functions) {
      find_functions_for_function_pointer (symbol_table,
                                           ns,
                                           functions,
                                           message_handler,
                                           target,
                                           type_map,
                                           address_taken);
    };

  for (const auto &root : roots) {
    const irep_idt &iden = root;
    produce_node_rec (goto_functions, ns, iden, graph,
                      omitted_functions, omit_function_pointers, 
                      find_functions_for_fp);
  }

}

std::string color_of_score (int score) {
  int s = 255 - score;
  std::stringstream stream;
  // Red
  stream << std::hex << 255;
  // Green
  if (s < 16) { stream << 0 << s; } else { stream << s; }
  // Blue
  if (s < 16) { stream << 0 << s; } else { stream << s; }
  std::string color( stream.str() );
  return color;
}

std::string color_of_score (int score1, int score2) { 
  int s1 = 255 - score1;
  int s2 = 255 - score2;
 std::stringstream stream;
  // Red
  stream << std::hex << 255;
  // Green
  if (s1 < 16) { stream << 0 << s1; } else { stream << s1; }
  // Blue
  if (s2 < 16) { stream << 0 << s2; } else { stream << s2; }
  std::string color( stream.str() );
  return color;
}

void compute_metrics (const complexity_grapht &graph,
                      std::map<irep_idt, func_metricst> &metrics,
                      const bool use_symex_info,
                      const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
                      const bool use_solver_info,
                      const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info) {
  for (const auto &it : graph.node_map) {
    const complexity_grapht::nodet node = it.second;
    func_metricst &m = metrics.find(node.name)->second;

    m.num_func_pointer_calls = num_func_pointer_calls (node.instructions);
    m.function_size = function_size (node.instructions);
    m.num_complex_user_ops = num_complex_user_ops (node.instructions);
    m.num_complex_cbmc_ops = num_complex_cbmc_ops (node.instructions);
    m.num_loops = num_loops (node.instructions);

    if (use_symex_info) {
      m.symex_info = aggregate_instr_info<symex_infot> (node.instructions, instr_symex_info);
    }
    if (use_solver_info) {
      m.solver_info = aggregate_instr_info<solver_infot> (node.instructions, instr_solver_info);
    }
    m.use_symex_info = use_symex_info;
    m.use_solver_info = use_solver_info;
  }
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
}

void compute_scores (std::map<irep_idt, func_metricst> &metrics,
                     std::map<irep_idt, int> &scores,
                     const bool use_symex_info,
                     const bool use_solver_info) {
  int w_num_func_pointer_calls = 5;
  int w_function_size = 1;
  int w_num_complex_user_ops = 5;
  int w_num_complex_cbmc_ops = 5;
  int w_num_loops = 15;
  int w_avg_time_per_symex_step = 0; // 1 ? use_symex_info : 0;

  for (auto it = metrics.begin(); it != metrics.end(); it++) {
    const irep_idt &name = it->first;
    const func_metricst &m = it->second;
    int score = w_num_func_pointer_calls * m.num_func_pointer_calls
              + w_function_size * m.function_size
              + w_num_complex_user_ops * m.num_complex_user_ops
              + w_num_complex_cbmc_ops * m.num_complex_cbmc_ops
              + w_num_loops * m.num_loops
              + w_avg_time_per_symex_step * (int)m.avg_time_per_symex_step()/10000;
    scores.find(name)->second = score;
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

std::string instruction_string (const goto_programt::instructiont instruction) {
  std::stringstream out;
  if(instruction.is_target())
    out << std::setw(6) << instruction.target_number << ": ";
  else
    out << "        ";

  switch(instruction.type())
  {
  case NO_INSTRUCTION_TYPE:
    out << "NO INSTRUCTION TYPE SET";
    break;

  case GOTO:
  case INCOMPLETE_GOTO:
    if(!instruction.condition().is_true())
    {
      out << "IF " << format(instruction.condition()) << " THEN ";
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

    break;

  case OTHER:
    if(instruction.get_other().id() == ID_code)
    {
      const auto &code = instruction.get_other();
      if(code.get_statement() == ID_array_copy)
      {
        out << "ARRAY_COPY " << format(code.op0()) << ' ' << format(code.op1());
        break;
      }
      else if(code.get_statement() == ID_array_replace)
      {
        out << "ARRAY_REPLACE " << format(code.op0()) << ' '
            << format(code.op1());
        break;
      }
      else if(code.get_statement() == ID_array_set)
      {
        out << "ARRAY_SET " << format(code.op0()) << ' ' << format(code.op1());
        break;
      }
      else if(code.get_statement() == ID_havoc_object)
      {
        out << "HAVOC_OBJECT " << format(code.op0());
        break;
      }
      else if(code.get_statement() == ID_fence)
      {
        out << "FENCE";
        if(code.get_bool(ID_WWfence))
          out << " WW";
        if(code.get_bool(ID_RRfence))
          out << " RR";
        if(code.get_bool(ID_RWfence))
          out << " RW";
        if(code.get_bool(ID_WRfence))
          out << " WR";
        break;
      }
      else if(code.get_statement() == ID_input)
      {
        out << "INPUT";
        for(const auto &op : code.operands())
          out << ' ' << format(op);
        break;
      }
      else if(code.get_statement() == ID_output)
      {
        out << "OUTPUT " << format(code.op0());
        break;
      }
      // fallthrough
    }

    out << "OTHER "; // FIXME << format(instruction.get_other());
    break;

  case SET_RETURN_VALUE:
    out << "SET RETURN VALUE " << format(instruction.return_value());
    break;

  case DECL:
    out << "DECL " << format(instruction.decl_symbol()) << " : "
        << format(instruction.decl_symbol().type());
    break;

  case DEAD:
    out << "DEAD " << format(instruction.dead_symbol());
    break;

  case FUNCTION_CALL:
    out << "CALL ";
    {
      if(instruction.call_lhs().is_not_nil())
        out << format(instruction.call_lhs()) << " := ";
      out << format(instruction.call_function());
      out << '(';
      bool first = true;
      for(const auto &argument : instruction.call_arguments())
      {
        if(first)
          first = false;
        else
          out << ", ";
        out << format(argument);
      }
      out << ')';
    }
    break;

  case ASSIGN:
    out << "ASSIGN " << format(instruction.assign_lhs())
        << " := " << format(instruction.assign_rhs());
    break;

  case ASSUME:
  case ASSERT:
    if(instruction.is_assume())
      out << "ASSUME ";
    else
      out << "ASSERT ";

    {
      // FIXME
      //out << format(instruction.condition());
      //
      //const irep_idt &comment = instruction.source_location().get_comment();
      //if(!comment.empty())
      //  out << " // " << comment;
    }

    break;

  case SKIP:
    out << "SKIP";
    break;

  case END_FUNCTION:
    out << "END_FUNCTION";
    break;

  case LOCATION:
    out << "LOCATION";
    break;

  case THROW:
    out << "THROW";

    {
      const irept::subt &exception_list =
        instruction.code().find(ID_exception_list).get_sub();

      for(const auto &ex : exception_list)
        out << " " << ex.id();
    }

    if(instruction.code().operands().size() == 1)
      out << ": " << format(instruction.code().op0());
    break;

  case CATCH:
  {
    if(instruction.code().get_statement() == ID_exception_landingpad)
    {
      const auto &landingpad = to_code_landingpad(instruction.code());
      out << "EXCEPTION LANDING PAD (" << format(landingpad.catch_expr().type())
          << ' ' << format(landingpad.catch_expr()) << ")";
    }
    else if(instruction.code().get_statement() == ID_push_catch)
    {
      out << "CATCH-PUSH ";

      unsigned i=0;
      const irept::subt &exception_list =
        instruction.code().find(ID_exception_list).get_sub();
      DATA_INVARIANT(
        instruction.targets.size() == exception_list.size(),
        "unexpected discrepancy between sizes of instruction"
        "targets and exception list");
      for(goto_programt::instructiont::targetst::const_iterator
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
    else if(instruction.code().get_statement() == ID_pop_catch)
    {
      out << "CATCH-POP";
    }
    else
    {
      UNREACHABLE;
    }
    out << "CATCH";
    break;
  }

  case ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN";
    break;

  case ATOMIC_END:
    out << "ATOMIC_END";
    break;

  case START_THREAD:
    out << "START THREAD "
        << instruction.get_target()->target_number;
    break;

  case END_THREAD:
    out << "END THREAD";
    break;
  }
  return out.str();

}


void compute_top_sort_node (const complexity_grapht &graph,
                            std::vector<irep_idt> &top_sort,
                            std::set<irep_idt> &seen,
                            const irep_idt &node) {
  if (seen.find(node) == seen.end()) {
    seen.insert (node);
    const auto &edge_map2 = graph.edge_map.find (node)->second;
    for (const auto &it2 : edge_map2) {
      const irep_idt other = it2.first;
      compute_top_sort_node (graph, top_sort, seen, other);
    }
    top_sort.push_back (node);
  }
}

void compute_top_sort (const complexity_grapht &graph,
                       std::vector<irep_idt> &top_sort) {
  std::set<irep_idt> seen;
  for (const auto &it : graph.edge_map) {
    const irep_idt node = it.first;
    if (seen.find(node) == seen.end()) {
      compute_top_sort_node (graph, top_sort, seen, node);
    }
  }
  std::reverse(top_sort.begin(), top_sort.end());
}

// assumes no cycles
void count_num_paths (const complexity_grapht &graph,
                      const std::vector<irep_idt> &top_sort,
                      std::map<irep_idt, int> &num_paths) {

  for (const irep_idt &node : top_sort) { 
    int path_count = 0;
    for (const auto &it : graph.dual_edge_map.find(node)->second) {
      const irep_idt other = it.first;
      // TODO: cycles
      path_count += num_paths.find(other) == num_paths.end() ? 0 : num_paths.find(other)->second;
    }
    // source nodes have a path count of 1
    if (path_count == 0) {
      path_count = 1;
    }
    num_paths.insert ({node, path_count});
  }
}

void compute_dominated_nodes_node (const complexity_grapht &graph,
                                   std::set<irep_idt> &dominated_nodes,
                                   const irep_idt node,
                                   const bool bypass) {
  
  bool all_backwards_edges_dominated = true;
  if (!bypass) {
    for (const auto &it : graph.dual_edge_map.find(node)->second) {
      const irep_idt other = it.first;
      if (dominated_nodes.find(other) != dominated_nodes.end()) {
        all_backwards_edges_dominated = false;
        break;
      }
    }
  }

  if (all_backwards_edges_dominated) {
    dominated_nodes.insert (node);
    for (const auto &it : graph.edge_map.find(node)->second) {
      const irep_idt other = it.first;
      compute_dominated_nodes_node (graph, dominated_nodes, other, false);
    }
  } 
}

// inefficient because it'll touch nodes multiple times.
void compute_dominated_nodes (const complexity_grapht &graph,
                              std::map<irep_idt, std::set<irep_idt>> &dominated_nodes) {
  for (const auto &it : graph.node_map) {
    const irep_idt node = it.first;
    dominated_nodes.insert ({node, std::set<irep_idt>()});
    std::set<irep_idt> &nodes = dominated_nodes.find(node)->second;
    compute_dominated_nodes_node (graph, nodes, node, true);
  }
}

void compute_reachable_nodes_node (const complexity_grapht &graph,
                                   std::set<irep_idt> &reachable_nodes,
                                   const irep_idt node) {
  
  if (reachable_nodes.find(node) == reachable_nodes.end()) {
    reachable_nodes.insert (node);
    for (const auto &it : graph.edge_map.find(node)->second) {
      const irep_idt other = it.first;
      compute_reachable_nodes_node (graph, reachable_nodes, other);
    }
  } 
}

// inefficient because it'll touch nodes multiple times.
void compute_reachable_nodes (const complexity_grapht &graph,
                              std::map<irep_idt, std::set<irep_idt>> &reachable_nodes) {
  for (const auto &it : graph.node_map) {
    const irep_idt node = it.first;
    reachable_nodes.insert ({node, std::set<irep_idt>()});
    std::set<irep_idt> &nodes = reachable_nodes.find(node)->second;
    compute_reachable_nodes_node (graph, nodes, node);
  }
}


void globalize_scores (const complexity_grapht &graph,
                       const std::map<irep_idt, int> &scores, 
                       std::map<irep_idt, int> &global_scores) {
  std::vector<irep_idt> top_sort;
  compute_top_sort (graph, top_sort);
  std::map<irep_idt, int> num_paths;
  count_num_paths (graph, top_sort, num_paths);
  std::map<irep_idt, std::set<irep_idt>> dominated_nodes;
  compute_dominated_nodes (graph, dominated_nodes);
  std::map<irep_idt, std::set<irep_idt>> reachable_nodes;
  compute_reachable_nodes (graph, reachable_nodes);
  
  for (const irep_idt &node : top_sort) {
    int paths = num_paths.find (node)->second;
    int base_score = 0;
    //std::set<irep_idt> &other_nodes = dominated_nodes.find(node)->second;
    std::set<irep_idt> &other_nodes = reachable_nodes.find(node)->second;
    for (const irep_idt &other : other_nodes) {
      base_score += scores.find(other)->second;
    }
    int global_score = base_score * paths;
    global_scores.find (node)->second = global_score;
  }

}

void replace_all_substrings (std::string& str, const std::string& from, const std::string& to) {
  int index = 0;
  while (true) {
     index = str.find(from, index);
     if (index == std::string::npos) break;
     str.replace(index, from.length(), to);
     index += from.length();
  }
}

void dump_html_table_entry (std::ostream &out, const std::string &text, const std::string &color) {
  out << "<tr><td align=\"text\"";
  out << " bgcolor=\"#" << color << "\"";
  out << ">"; // style=\"font-family:'Courier', monospace\">";
  out << text;
  out << "<br align=\"left\" /></td></tr>";
}

void dump_instruction 
  (const irep_idt &name,
   const goto_programt::const_targett &target,
   std::ostream &out,
   const namespacet &ns,
   const bool use_symex_info,
   const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
   const symex_infot &max_symex_info,
   const bool use_solver_info,
   const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
   const solver_infot &max_solver_info) {

  int s1 = 0;
  if (use_symex_info) {
    auto symex_info = instr_symex_info.find (target);
    if (symex_info != instr_symex_info.end()) {
      // milliseconds
      // double avg_time_per_step = (symex_info->second.duration / (double) symex_info->second.steps) / 1000000.0;
      double duration = symex_info->second.duration;
      s1 = std::max(0, std::min (255, (int) (255.0 * duration / max_symex_info.duration)));
      /*
      int steps = symex_info->second.steps;
      s1 = std::max(0, std::min (255, (int) ((255 * steps) / max_symex_info.steps)));
      */
    }
  }


  int s2 = 0;
  if (use_solver_info) {
    auto solver_info = instr_solver_info.find (target);
    if (solver_info != instr_solver_info.end()) {
      int clauses = solver_info->second.clauses;
      s2 = std::max(0, std::min (255, 255 * clauses / max_solver_info.clauses));
    }
  }
  std::string color = color_of_score (s1, s2);
  //out << "fillcolor=" << "\"#" << color << "\",";
    
  const goto_programt::instructiont &instruction = *target;
  std::string instr_str = instruction_string (instruction);
  replace_all_substrings (instr_str, "$", "&dollar;");
  // apparently not necessary, and will break things.
  // replace_all_substrings (instr_str, ":", "&colon;");
  replace_all_substrings (instr_str, "\"", "&quot;");
  replace_all_substrings (instr_str, ">", "&gt;");
  replace_all_substrings (instr_str, "<", "&lt;");

  dump_html_table_entry (out, instr_str, color);

}

void dump_instructions 
  (const complexity_grapht::nodet &node,
   const std::map<irep_idt, int> dot_node_naming,
   const goto_functiont::parameter_identifierst &params,
   const std::vector<std::vector<goto_programt::const_targett>> &instructions,
   std::ostream &out,
   const namespacet &ns,
   const bool use_symex_info,
   const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
   const symex_infot &max_symex_info,
   const bool use_solver_info,
   const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
   const solver_infot &max_solver_info) {

  const irep_idt &name = node.name;

  out << name << "_body"
      << "[";

  out << "shape=rectangle,"; //plaintext,";
  out << "fontsize=" << 4 << ",";
  out << "fontname=\"Courier\",";
  out << "label=<";
  out << " <table border=\"0\">";
  out << "<tr><td align=\"text\">" << node.display_name << "(";
  int param_index = 0;
  for (const auto &param : params) {
    out << ((param_index == 0) ? "" : ", ") << param;
    param_index++;
  }
  out << ")";
  out << "<br align=\"left\" /></td></tr>";

  for (const auto &insts : instructions) {
    for (const auto &target : insts) {
      dump_instruction (name, target, out, ns, 
                        use_symex_info, instr_symex_info, max_symex_info,
                        use_solver_info, instr_solver_info, max_solver_info);
    }

    // dump a '...' line
    dump_html_table_entry (out, "...", "FFFFFF");
  }

  out << "</table> ";
  out << ">]" << ";\n";

  // add an edge between the function node and the body node, so that
  // the body gets placed beneath the function node.
  out << dot_node_naming.find(name)->second <<  " -> " << name << "_body"
      << " ["
      << "style=invis"
      << "];\n";
}
                    

void dump_nodes
(const complexity_grapht &graph,
 const std::map<irep_idt, int> dot_node_naming,
 std::ostream &out, 
 const optionst &options,
 const namespacet &ns,
 const goto_functionst &goto_functions,
 const std::map<irep_idt, func_metricst> &metrics,
 const std::map<irep_idt, int> &scores,
 const std::map<irep_idt, int> &globalized_scores,
 const bool use_symex_info,
 const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
 const symex_infot &max_symex_info,
 const bool use_solver_info,
 const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
 const solver_infot &max_solver_info) {

  for (const auto &it : graph.node_map) {
    const complexity_grapht::nodet &node = it.second;
    const irep_idt &name = node.name;


    // dump the high-symex nodes
    
    //if (use_symex_info) {
    //  for (const auto target : node.instructions()) {
    //    auto symex_info = instr_symex_info.find (target);
    //    if (symex_info != instr_symex_info.end()) {
    //      // milliseconds
    //      double avg_time_per_step = (symex_info->second.duration / (double) symex_info->second.steps) / 1000000.0;
    //      if (avg_time_per_step > 0.1) {
    //        out << "// HIGH SYMEX: num symex steps: " << avg_time_per_step << "\n";
    //        out << "/* "; 
    //        body.output_instruction(ns, f, out, *target);
    //        out << "*/\n";
    //      }
    //    }
    //  }
    //}

    std::string color; 
    // int size = (8 + sqrt(metrics.find(name)->second.function_size));
    std::string size;
    std::string style;
    std::string shape;
    std::stringstream label;
    switch (node.node_type) 
    {
    case complexity_grapht::nodet::node_typet::FUNCTION:
      shape = node.has_property("no_body") ? "Mdiamond" :
              node.has_property("private") ? "ellipse" : "rect";
      //color = color_of_score (globalized_scores.find (name)->second);
      color = color_of_score (scores.find (name)->second); // , globalized_scores.find (name)->second);
      style = "filled";
      size = "8";
      label << node.display_name;
      label << " <br/> ";
      metrics.find(name)->second.dump_html (label);
      //label << " <br/> local complexity: " << scores.find (name)->second;
      //label << " <br/> global complexity: " << globalized_scores.find (name)->second;
      break;
    case complexity_grapht::nodet::node_typet::FUNCTION_POINTER:
      shape = "rarrow";
      color = "ffffff";
      style = "filled";
      size = "8";
      label << node.display_name;
      break;
    case complexity_grapht::nodet::node_typet::LOOP:
      shape = "doublecircle";
      color = "ffffff";
      style = "filled";
      size = "8";
      label << node.display_name;
      break;
    default:
      break;
    }

    //out << "subgraph {rank=same;color=blue;\n";

    out << "// " << node.display_name << "\n";
    out << dot_node_naming.find(name)->second
        << " [" 
        << "label=" << "<" << label.str() << ">" << ","
        << "shape=" << shape << ","
        << "style=" << style << ","
        << "fillcolor=" << "\"#" << color << "\","
        << "fontsize=" << size
        << "];\n\n";

    
    if (options.get_bool_option ("complexity-graph-instructions")) {
      // TODO: inefficient
      const auto sorted = goto_functions.sorted();
      for (const auto &fun : sorted) { 
        if (fun->first == node.name) {
          const auto &func = fun->second;
          const goto_functiont::parameter_identifierst &params = func.parameter_identifiers;
          dump_instructions(node, dot_node_naming, params, node.instructions, out, ns, 
                            use_symex_info, instr_symex_info, max_symex_info,
                            use_solver_info, instr_solver_info, max_solver_info);
          break;
        }
      }
    }
    //out << "}\n";
  }
}

void dump_edges 
(const complexity_grapht &graph,
 const std::map<irep_idt, int> dot_node_naming,
 std::ostream &out, 
 const optionst &options,
 const namespacet &ns,
 std::map<irep_idt, func_metricst> &metrics,
 std::map<irep_idt, int> &scores,
 const bool use_symex_info,
 const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
 const symex_infot &max_symex_info,
 const bool use_solver_info,
 const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
 const solver_infot &max_solver_info) {

  for (const auto &it : graph.edge_map) {
    complexity_grapht::nodet node1 = graph.find_node (it.first);
    const std::map<irep_idt, complexity_grapht::edget> &edge_map2 = it.second;
    for (const auto &it2 : edge_map2) {
      complexity_grapht::nodet node2 = graph.find_node (it2.first);
      out << "// " << node1.display_name << " -> " << node2.display_name << "\n";
      out << dot_node_naming.find(node1.name)->second << " -> " << dot_node_naming.find(node2.name)->second << ";\n\n";

      /*
    std::string color = "0000ff";
    std::string opacity = "18";
                 << " ["
                 << "color=" << "\"#" << color << opacity << "\""
                 << "];\n";
      */
    }
  }


}

void parse_string_list (std::string lst, std::vector<irep_idt> &use, const std::string &delim) {

    while (lst.length() != 0) {
      const auto idx = lst.find(delim);
      const std::string s = lst.substr (0, idx);
      const irep_idt irep_s = s;
      use.push_back(irep_s);

      lst = lst.substr (idx + delim.length());
    }
}

void dump_complexity_graph(
  const optionst &options,
  const std::string &path,
  const abstract_goto_modelt &goto_model,
  message_handlert &message_handler,
  const bool use_symex_info,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
  const bool use_solver_info,
  const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info)
{
  // null_message_handlert message_handler = null_message_handlert();

  std::cout << "Writing complexity graph to " << path << "\n";

  std::vector<irep_idt> roots;
  parse_string_list (options.get_option ("complexity-graph-roots"), roots, ",");

  std::vector<irep_idt> omitted_functions_lst;
  parse_string_list (options.get_option ("complexity-graph-omit-function"), omitted_functions_lst, ",");
  std::set<irep_idt> omitted_functions;
  for (const irep_idt &f : omitted_functions_lst) {
    omitted_functions.insert (f);
  }


  bool omit_function_pointers = options.get_bool_option ("complexity-graph-omit-function-pointers");

  const namespacet ns(goto_model.get_symbol_table());
  const goto_functionst &goto_functions = goto_model.get_goto_functions();

  std::ofstream outf (path.c_str()); 
  std::ostream &out = outf;

  const auto sorted = goto_functions.sorted();

  complexity_grapht graph;
  if (roots.size() == 0) {
    for (const auto &fun : sorted) {
      const auto &name = ns.lookup(fun->first).name;
      std::stringstream stream;
      stream << name;
      roots.push_back(stream.str());
    }
    // goto_functions.entry_point();
  }

  std::map<irep_idt, code_typet> type_map;
  std::unordered_set<irep_idt> address_taken;
  // std::cout << "setup begin" << "\n";
  function_pointer_setup (goto_model.get_symbol_table(), ns, goto_functions, type_map, address_taken);
  // std::cout << "type map size: " << type_map.size() << "\n";
  // std::cout << "address taken size: " << address_taken.size() << "\n";
  // std::cout << "setup end" << "\n";

  //std::cout << "produce begin" << "\n";
  produce_graph (goto_model.get_symbol_table(), ns, message_handler, type_map, address_taken,
                 roots, goto_functions, graph,
                 omit_function_pointers, omitted_functions);
  //std::cout << "produce end" << "\n";

  // remove_functions_no_body(ns, goto_functions, use);

  out << "digraph G {\n\n";
  out << "// roots:";
  for (const auto &root : roots) {
    out << " " << root;
  }
  if (roots.size() == 0) {
    out << "all functions";
  }
  out << "\n\n";

  out << "// omitted_functions:";
  for (const auto &f : omitted_functions) {
    out << " " << f;
  }
  out << "\n\n";

  if (omit_function_pointers) {
    out << "// omitting function pointers" << "\n\n";
  }

  out << "rankdir=\"LR\";\n\n";

  std::map<irep_idt, int> scores;
  std::map<irep_idt, int> globalized_scores;
  std::map<irep_idt, func_metricst> metrics;
  for (const auto &it : graph.node_map) {
    const irep_idt &name = it.first;
    metrics.insert({name, func_metricst()});
    scores.insert({name, 0});
    globalized_scores.insert({name, 0});
  }

  // initialize scores
  //std::cout << "scores begin" << "\n";
  compute_metrics (graph, metrics, 
                   use_symex_info, instr_symex_info, 
                   use_solver_info, instr_solver_info);
  compute_scores (metrics, scores, use_symex_info, use_solver_info);
  globalize_scores (graph, scores, globalized_scores);
  //std::cout << "scores end" << "\n";
  normalize_scores (globalized_scores);
  normalize_scores (scores);

  
  symex_infot max_symex_info;
  if (use_symex_info) {
    for(const auto &fun : sorted) {
      forall_goto_program_instructions(target, fun->second.body) {
        const auto &symex_info = instr_symex_info.find (target);
        if (symex_info != instr_symex_info.end()) {
          max_symex_info.duration = std::max(max_symex_info.duration, symex_info->second.duration);
          max_symex_info.steps = std::max(max_symex_info.steps, symex_info->second.steps);
        }
      }
    }
  }

  solver_infot max_solver_info;
  if (use_solver_info) {
    for(const auto &fun : sorted) {
      forall_goto_program_instructions(target, fun->second.body) {
        const auto &solver_info = instr_solver_info.find (target);
        if (solver_info != instr_solver_info.end()) {
          max_solver_info.clauses = std::max(max_solver_info.clauses, solver_info->second.clauses);
          max_solver_info.literals = std::max(max_solver_info.literals, solver_info->second.literals);
          max_solver_info.variables = std::max(max_solver_info.variables, solver_info->second.variables);
        }
      }
    }
  }

  std::map<irep_idt, int> dot_node_naming;
  {
    int index = 0;
    for (const auto &it : graph.node_map) {
      dot_node_naming.insert ({it.first, index});
      index++;
    }
  }

  //std::cout << "dump begin" << "\n";

  dump_nodes (graph, dot_node_naming, out, options, ns, goto_functions, metrics, scores, globalized_scores,
              use_symex_info, instr_symex_info, max_symex_info,
              use_solver_info, instr_solver_info, max_solver_info);

  dump_edges (graph, dot_node_naming, out, options, ns, metrics, scores,
              use_symex_info, instr_symex_info, max_symex_info,
              use_solver_info, instr_solver_info, max_solver_info);
  //std::cout << "dump end" << "\n";

  out << "} // end digraph G\n";

}


void show_complexity_graph(
  const optionst &options,
  const abstract_goto_modelt &goto_model,
  const std::string &path,
  message_handlert &message_handler)
{
  const std::map<goto_programt::const_targett, symex_infot> instr_symex_info;
  const bool use_symex_info = false;
  const std::map<goto_programt::const_targett, solver_infot> instr_solver_info;
  const bool use_solver_info = false;

  dump_complexity_graph(
    options,
    path,
    goto_model,
    message_handler, 
    use_symex_info,
    instr_symex_info,
    use_solver_info,
    instr_solver_info);
}
  
void show_complexity_graph(
  const optionst &options,
  const abstract_goto_modelt &goto_model,
  const std::string &path,
  message_handlert &message_handler,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info)
{
  const bool use_symex_info = true;
  const std::map<goto_programt::const_targett, solver_infot> instr_solver_info;
  const bool use_solver_info = false;
  dump_complexity_graph(
    options,
    path,
    goto_model,
    message_handler, 
    use_symex_info,
    instr_symex_info,
    use_solver_info,
    instr_solver_info);
}
  
void show_complexity_graph(
  const optionst &options,
  const abstract_goto_modelt &goto_model,
  const std::string &path,
  message_handlert &message_handler,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
  const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info)
{
  const bool use_symex_info = true;
  const bool use_solver_info = true;
  dump_complexity_graph(
    options,
    path,
    goto_model,
    message_handler, 
    use_symex_info,
    instr_symex_info,
    use_solver_info,
    instr_solver_info);
}
  

  
