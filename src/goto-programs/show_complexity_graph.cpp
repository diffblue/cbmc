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

// is this function a private function?
// does name look like "__CPROVER_file_local_{filename}_c_{name}";
// \param name: the name to inspect
bool is_private (const irep_idt &name)
{

  const std::string str (name.c_str(), name.size());

  return (str.find ("__CPROVER_file_local_") != std::string::npos);
}

// produces a name without CBMC internal naming effects
// \param name: the name to normalize
std::string normalize_name (const irep_idt &name)
{
  // "__CPROVER_file_local_{filename}_c_{name}";

  const std::string str (name.c_str(), name.size());

  if (str.find ("__CPROVER_file_local_") != std::string::npos)
  {
    return str.substr (str.find ("_c_") + 3);

  }

  return str;
}

// replaces all substrings in the string with the provided string
// \param str: the string to look in
// \param from: the substring to look for
// \param to: the replacement
void replace_all_substrings (std::string &str, const std::string &from, const std::string &to)
{
  size_t index = 0;
  while (true)
  {
     index = str.find(from, index);
     if (index == std::string::npos) break;
     str.replace(index, from.length(), to);
     index += from.length();
  }
}

void normalize_html (std::string &str) 
{
  // other characters which don't seem to cause a problem: {"$", "&dollar"}, {":", "&colon"}
  replace_all_substrings (str, "\"", "&quot;");
  replace_all_substrings (str, ">", "&gt;");
  replace_all_substrings (str, "<", "&lt;");
  replace_all_substrings (str, "\n", "<br/>");
}

// initialize the data structures used for function pointer target detection
void function_pointer_setup (const symbol_tablet &symbol_table,
                             const namespacet &ns,
                             const goto_functionst &goto_functions,
                             std::map<irep_idt, code_typet> &type_map,
                             std::unordered_set<irep_idt> &address_taken)
{

  for(const auto &s : symbol_table.symbols)
  {
    compute_address_taken_functions(s.second.value, address_taken);
  }

  compute_address_taken_functions(goto_functions, address_taken);

  for(const auto &gf_entry : goto_functions.function_map)
  {
    type_map.emplace(
      gf_entry.first, to_code_type(ns.lookup(gf_entry.first).type));
  }

}

// initialize the data structures used for function pointer target detection
// adapted from goto-programs/remove_function_pointers.c
void find_functions_for_function_pointer (
  const symbol_tablet &symbol_table,
  const namespacet &ns,
  remove_const_function_pointerst::functionst &functions,
  message_handlert &message_handler,
  const goto_programt::const_targett &target,
  const std::map<irep_idt, code_typet> &type_map,
  const std::unordered_set<irep_idt> &address_taken)
{

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


// populates the nodes of the grapph recursively
void produce_node_rec (
  const goto_functionst &goto_functions,
  const namespacet &ns,
  const irep_idt name,
  complexity_grapht &graph,
  const std::set<irep_idt> &lib_funcs,
  const std::set<irep_idt> &omitted_functions,
  const bool omit_function_pointers,
  std::function<void(goto_programt::const_targett&, remove_const_function_pointerst::functionst&)> find_functions_for_function_pointer)
{
  if (!(graph.has_node (name)))
  {
    std::string display_name = normalize_name(name);
    normalize_html(display_name);
    complexity_grapht::nodet &node = graph.add_node (complexity_grapht::nodet (name, display_name, complexity_grapht::nodet::node_typet::FUNCTION));

    if (lib_funcs.find(name) != lib_funcs.end())
    {
      node.add_property ("library");
    }

    if (is_private(name))
    {
      node.add_property ("private");
    }

    const auto fun = goto_functions.function_map.find(name);
    if (fun != goto_functions.function_map.end())
    {
      bool has_body = fun->second.body_available();

      if (has_body)
      {
        auto target = fun->second.body.instructions.begin();
        auto end = fun->second.body.instructions.end();
        node.instructions.push_back(std::vector<goto_programt::const_targett>());

        while (target != end)
        {
          // FUTURE: can segment function bodies into loops
          node.instructions[0].push_back (target);

          if(target->is_function_call())
          {
            // normal function calls
            if (target->call_function().id() != ID_dereference)
            {
              const irep_idt call = ns.lookup(to_symbol_expr(target->call_function())).name;

              std::stringstream stream;
              stream << call;
              std::string str_call = stream.str();

              if (omitted_functions.find(str_call) == omitted_functions.end())
              {
                if (!graph.has_node(call))
                {
                  produce_node_rec (goto_functions, ns, call, graph, lib_funcs,
                                    omitted_functions,
                                    omit_function_pointers, find_functions_for_function_pointer);
                }
                graph.add_edge (node.name, call);
              }
            } else {
              // function pointer calls
              if (!omit_function_pointers)
              {
                const exprt &pointer = to_dereference_expr(target->call_function()).pointer();
                std::stringstream stream;
                stream << "\"" << format(pointer) << "\"";


                std::stringstream rhs_stream;
                rhs_stream << node.name << "." << stream.str();
                std::string rhs = rhs_stream.str();
                std::string rhs_display = stream.str();
                normalize_html(rhs_display);

                graph.add_node (complexity_grapht::nodet (rhs, rhs_display, complexity_grapht::nodet::node_typet::FUNCTION_POINTER));
                graph.add_edge (node.name, rhs);

                remove_const_function_pointerst::functionst functions;

                find_functions_for_function_pointer (target, functions);
                for (const symbol_exprt &function : functions)
                {
                  const irep_idt &name = function.get_identifier();
                  if (!graph.has_node (name))
                  {
                    std::string display_name = normalize_name (name);
                    normalize_html(display_name);
                    graph.add_node (complexity_grapht::nodet (name, display_name, complexity_grapht::nodet::node_typet::FUNCTION));
                  }

                  graph.add_edge (rhs, name);
                }
              }
            }
          }

          target++;
        }

      } else
      {
        node.add_property ("no_body");
      }
    } else
    {
      node.add_property ("no_definition");
    }
  }
}

// populates the graph with nodes and edges based on the given collection of goto_functions
// \param lib_funcs: a set of library functions
// \param omitted_functions: a set of functions to omit from the graph
// \param omit_function_pointers: whether function pointers should be included in the graph
// \param find_functions_for_function_pointer: produces the targets that
//   a function pointer can resolve to
void produce_graph (
  const symbol_tablet &symbol_table,
  const namespacet &ns,
  message_handlert& message_handler,
  const std::map<irep_idt, code_typet> &type_map,
  const std::unordered_set<irep_idt> &address_taken,
  const std::vector<irep_idt> &roots,
  const goto_functionst &goto_functions,
  complexity_grapht &graph,
  const std::set<irep_idt> &lib_funcs,
  const bool omit_function_pointers,
  const std::set<irep_idt> &omitted_functions)
{

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

  for (const auto &root : roots)
  {
    const irep_idt &iden = root;
    produce_node_rec (goto_functions, ns, iden, graph, lib_funcs,
                      omitted_functions, omit_function_pointers,
                      find_functions_for_fp);
  }

}

// provides a color given the numeric input.
// color ranges from white to red
std::string color_of_score (size_t score)
{
  size_t s = 255 - score;
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

// provides a color given the numeric inputs.
// color ranges from white to magenta to yellow
std::string color_of_score (size_t score1, size_t score2)
{
  size_t s1 = 255 - score1;
  size_t s2 = 255 - score2;
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

// populate the metrics for each node in the graph
void compute_metrics (const complexity_grapht &graph,
                      std::map<irep_idt, func_metricst> &metrics,
                      const std::set<irep_idt> &lib_funcs,
                      const bool use_symex_info,
                      const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
                      const bool use_solver_info,
                      const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info)
{
  for (const auto &it : graph.node_map)
  {
    const complexity_grapht::nodet node = it.second;
    func_metricst &m = metrics.find(node.name)->second;

    m.num_func_pointer_calls = num_func_pointer_calls (node.instructions);
    m.function_size = function_size (node.instructions);
    m.num_complex_user_ops = num_complex_user_ops (node.instructions);
    m.num_complex_lib_funcs = num_complex_lib_funcs (node.instructions, lib_funcs);
    m.num_complex_cbmc_ops = num_complex_cbmc_ops (node.instructions);
    m.num_loops = num_loops (node.instructions);

    if (use_symex_info)
    {
      m.symex_info = aggregate_instr_info<symex_infot> (node.instructions, instr_symex_info);
    }
    if (use_solver_info)
    {
      m.solver_info = aggregate_instr_info<solver_infot> (node.instructions, instr_solver_info);
    }
    m.use_symex_info = use_symex_info;
    m.use_solver_info = use_solver_info;
  }
}

// normalize the score map
void normalize_scores (std::map<irep_idt, size_t> &scores)
{
  size_t max = 0;
  for (auto it = scores.begin(); it != scores.end(); it++)
  {
    max = std::max (max, it->second);
  }

  for (auto it = scores.begin(); it != scores.end(); it++)
  {
    // score between [0, inf)
    size_t score = it->second;
    // normalized score between [0, 255]
    float norm_score = 255.0 * ((float) score) / ((float) max);
    size_t normalized_score = std::min(255, std::max(0, (int) norm_score));
    it->second = normalized_score;
  }
}

// compute a score for each node based on the metrics
// currently uses a weighted sum
// does not use the solver or symex information at the moment
void compute_scores (std::map<irep_idt, func_metricst> &metrics,
                     std::map<irep_idt, size_t> &scores,
                     const bool use_symex_info,
                     const bool use_solver_info)
{
  size_t w_num_func_pointer_calls = 5;
  size_t w_function_size = 1;
  size_t w_num_complex_user_ops = 5;
  size_t w_num_complex_lib_funcs = 50;
  size_t w_num_complex_cbmc_ops = 5;
  size_t w_num_loops = 20;

  for (auto it = metrics.begin(); it != metrics.end(); it++)
  {
    const irep_idt &name = it->first;
    const func_metricst &m = it->second;
    size_t score = w_num_func_pointer_calls * m.num_func_pointer_calls
                 + w_function_size * m.function_size
                 + w_num_complex_user_ops * m.num_complex_user_ops
                 + w_num_complex_lib_funcs * m.num_complex_lib_funcs
                 + w_num_complex_cbmc_ops * m.num_complex_cbmc_ops
                 + w_num_loops * m.num_loops;
    scores.find(name)->second = score;
  }
}

void compute_top_sort_rec (const complexity_grapht &graph,
                            std::vector<irep_idt> &top_sort,
                            std::set<irep_idt> &seen,
                            const irep_idt &node)
{
  if (seen.find(node) == seen.end())
  {
    seen.insert (node);
    const auto &edge_map2 = graph.edge_map.find (node)->second;
    for (const auto &it2 : edge_map2)
    {
      const irep_idt other = it2.first;
      compute_top_sort_rec (graph, top_sort, seen, other);
    }
    top_sort.push_back (node);
  }
}

// computes a topological sort of the graph, in the case it is acyclic.
void compute_top_sort (const complexity_grapht &graph,
                       std::vector<irep_idt> &top_sort)
{
  std::set<irep_idt> seen;
  for (const auto &it : graph.edge_map)
  {
    const irep_idt node = it.first;
    if (seen.find(node) == seen.end())
    {
      compute_top_sort_rec (graph, top_sort, seen, node);
    }
  }
  std::reverse(top_sort.begin(), top_sort.end());
}

// counts the number of paths to each node in the graph, assuming the graph is acyclic.
void count_num_paths (const complexity_grapht &graph,
                      const std::vector<irep_idt> &top_sort,
                      std::map<irep_idt, size_t> &num_paths)
{
  for (const irep_idt &node : top_sort)
  {
    size_t path_count = 0;
    for (const auto &it : graph.dual_edge_map.find(node)->second)
    {
      const irep_idt other = it.first;
      // deals with cycles in a degenerate way
      path_count += num_paths.find(other) == num_paths.end() ? 0 : num_paths.find(other)->second;
    }
    // source nodes have a path count of 1
    if (path_count == 0)
    {
      path_count = 1;
    }
    num_paths.insert ({node, path_count});
  }
}

// computes a globalized score for a node dependent on how many paths it took to get there
void globalize_scores (const complexity_grapht &graph,
                       const std::map<irep_idt, size_t> &scores,
                       std::map<irep_idt, size_t> &global_scores)
{
  std::vector<irep_idt> top_sort;
  compute_top_sort (graph, top_sort);
  std::map<irep_idt, size_t> num_paths;
  count_num_paths (graph, top_sort, num_paths);

  for (const irep_idt &node : top_sort)
  {
    size_t paths = num_paths.find (node)->second;
    size_t base_score = 0;

    for (const auto &it : graph.edge_map.find(node)->second)
    {
      const irep_idt other = it.first;
      base_score += global_scores.find(other)->second;
    }

    size_t global_score = base_score * paths;
    global_scores.find (node)->second = global_score;
  }

}

// dumps a valid HTML table entry with the given text to the given output stream.
void dump_html_table_entry (std::ostream &out, const std::string &text, const std::string &color)
{
  out << "<tr><td align=\"text\"";
  out << " bgcolor=\"#" << color << "\"";
  out << ">"; // style=\"font-family:'Courier', monospace\">";
  out << text;
  out << "<br align=\"left\" /></td></tr>";
}

// dumps an instruction to the given output stream, if it is determined to have high complexity.
// returns whether it was dumped.
bool dump_instruction
  (const irep_idt &name,
   const goto_programt::const_targett &target,
   const goto_programt &program,
   std::ostream &out,
   const namespacet &ns,
   const bool use_symex_info,
   const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
   const symex_infot &max_symex_info,
   const bool use_solver_info,
   const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
   const solver_infot &max_solver_info)
{

  size_t s_symex = 0;
  if (use_symex_info)
  {
    auto symex_info = instr_symex_info.find (target);
    if (symex_info != instr_symex_info.end())
    {
      double duration = symex_info->second.duration;
      double temp = 255.0 * duration / max_symex_info.duration;
      s_symex = std::max<size_t>(0, std::min<size_t> (255, temp));
    }
  }


  size_t s_solver = 0;
  if (use_solver_info)
  {
    auto solver_info = instr_solver_info.find (target);
    if (solver_info != instr_solver_info.end())
    {
      size_t clauses = solver_info->second.clauses;
      size_t temp = 255 * clauses / max_solver_info.clauses;
      s_solver = std::max<size_t>(0, std::min<size_t> (255, temp));
    }
  }
  std::string color = color_of_score (s_symex, s_solver);

  const goto_programt::instructiont &instruction = *target;
  std::stringstream instr_str_stream;
  irep_idt empty = "";
  program.output_instruction (ns, empty, instr_str_stream, instruction);
  std::string instr_str = instr_str_stream.str();
  normalize_html (instr_str);

  bool use_instruction = (s_symex > 8) || (s_solver > 8);
  if (use_instruction)
  {
    dump_html_table_entry (out, instr_str, color);
  }
  return use_instruction;

}

// dumps a vertex whose label contains all the high-complexity instructions associated with the given node.
// dumps an edge between the source node and the node for the body.
void dump_instructions
  (const complexity_grapht::nodet &node,
   std::map<irep_idt, size_t> &dot_node_naming,
   const goto_functiont::parameter_identifierst &params,
   const goto_programt &program,
   const std::vector<std::vector<goto_programt::const_targett>> &instructions,
   std::ostream &out,
   const namespacet &ns,
   const bool use_symex_info,
   const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
   const symex_infot &max_symex_info,
   const bool use_solver_info,
   const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
   const solver_infot &max_solver_info)
{

  const irep_idt &name = node.name;

  std::stringstream instructions_stream;
  bool any_used_instructions = false;

  size_t index = 0;
  for (const auto &insts : instructions)
  {
    for (const auto &target : insts)
    {
      any_used_instructions = any_used_instructions ||
        dump_instruction (name, target, program, instructions_stream, ns,
                          use_symex_info, instr_symex_info, max_symex_info,
                          use_solver_info, instr_solver_info, max_solver_info);
    }

    // dump a '...' line
    if (index != instructions.size() - 1)
    {
      dump_html_table_entry (out, "...", "FFFFFF");
    }

    ++index;
  }

  if (any_used_instructions)
  {
    std::stringstream body_name_stream;
    body_name_stream << name << "_body";
    const irep_idt body_name = body_name_stream.str();

    dot_node_naming.insert ({body_name, dot_node_naming.size()});

    out << dot_node_naming.find(body_name)->second
        << " [";

    out << "shape=rectangle,"; //plaintext,";
    out << "fontsize=" << 4 << ",";
    out << "fontname=\"Courier\",";
    out << "label=<";
    out << " <table border=\"0\"> ";
    out << instructions_stream.str();
    out << "</table> ";
    out << ">]" << ";\n\n";

    // add an edge between the function node and the body node, so that
    // the body gets placed beneath the function node.
    out << dot_node_naming.find(name)->second
        <<  " -> "
        << dot_node_naming.find(body_name)->second
        << " [arrowhead=none]"
        << "\n";
  }
}


// dumps all of the nodes in the graph to the output stream.
void dump_nodes
(const complexity_grapht &graph,
 std::map<irep_idt, size_t> &dot_node_naming,
 std::ostream &out,
 const bool include_instructions,
 const namespacet &ns,
 const goto_functionst &goto_functions,
 const std::map<irep_idt, func_metricst> &metrics,
 const std::map<irep_idt, size_t> &scores,
 const bool use_symex_info,
 const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
 const symex_infot &max_symex_info,
 const bool use_solver_info,
 const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
 const solver_infot &max_solver_info)
{

  for (const auto &it : graph.node_map)
  {
    const complexity_grapht::nodet &node = it.second;
    const irep_idt &name = node.name;

    std::string color = "000000";
    std::string fillcolor = "ffffff";
    std::string size = "8";
    std::string style = "filled";
    std::string shape;
    std::stringstream label;
    switch (node.node_type)
    {
    case complexity_grapht::nodet::node_typet::FUNCTION:
      shape = node.has_property("library") ? "pentagon" :
              node.has_property("no_body") ? "Mdiamond" :
              node.has_property("private") ? "ellipse" :
              "rect";
      if (node.has_property("library"))
      {
        color = "FF0000";
      }
      fillcolor = color_of_score (scores.find (name)->second);
      label << node.display_name;
      label << " <br/> ";
      if (!node.has_property ("no_body"))
      {
        metrics.find(name)->second.dump_html (label);
      }
      break;
    case complexity_grapht::nodet::node_typet::FUNCTION_POINTER:
      shape = "rarrow";
      fillcolor = "ffffff";
      label << node.display_name;
      break;
    case complexity_grapht::nodet::node_typet::LOOP:
      shape = "doublecircle";
      label << node.display_name;
      break;
    default:
      break;
    }

    out << "subgraph {rank=same;color=blue;\n";

    out << "// " << node.display_name << "\n";
    out << dot_node_naming.find(name)->second
        << " ["
        << "label=" << "<" << label.str() << ">" << ","
        << "shape=" << shape << ","
        << "style=" << style << ","
        << "color=" << "\"#" << color << "\","
        << "fillcolor=" << "\"#" << fillcolor << "\","
        << "fontsize=" << size
        << "];\n\n";


    if (include_instructions)
    {
      const auto fun = goto_functions.function_map.find(node.name);
      if (fun != goto_functions.function_map.end() && fun->second.body_available())
      {
        const auto &func = fun->second;
        const goto_functiont::parameter_identifierst &params = func.parameter_identifiers;
        const goto_programt &body = func.body;
        dump_instructions(node, dot_node_naming, params, body, node.instructions, out, ns,
                          use_symex_info, instr_symex_info, max_symex_info,
                          use_solver_info, instr_solver_info, max_solver_info);
      }
    }
    out << "}\n\n";
  }
}

// dumps all of the edges in the graph to the output stream.
void dump_edges (
  const complexity_grapht &graph,
  std::map<irep_idt, size_t> &dot_node_naming,
  std::ostream &out,
  const optionst &options,
  const namespacet &ns)
{

  for (const auto &it : graph.edge_map)
  {
    complexity_grapht::nodet node1 = graph.find_node (it.first);
    const std::map<irep_idt, complexity_grapht::edget> &edge_map2 = it.second;
    for (const auto &it2 : edge_map2)
    {
      complexity_grapht::nodet node2 = graph.find_node (it2.first);
      out << "// " << node1.display_name << " -> " << node2.display_name << "\n";
      out << dot_node_naming.find(node1.name)->second << " -> " << dot_node_naming.find(node2.name)->second << ";\n\n";
    }
  }


}

// parses a list of strings separated by the delimiter
// \param lst: the string to search through
// \param use: the container for the result
// \param delim: the delimiter to search for in lst
void parse_string_list (std::string lst, std::vector<irep_idt> &use, const std::string &delim)
{
    while (lst.length() != 0)
    {
      const auto idx = lst.find(delim);
      const std::string s = lst.substr (0, idx);
      const irep_idt irep_s = s;
      use.push_back(irep_s);

      lst = lst.substr (idx + delim.length());
    }
}

// constructs the complexity graph, placing the result in graph
void construct_complexity_graph (
  complexity_grapht &graph,
  const namespacet &ns,
  const goto_functionst &goto_functions,
  const symbol_tablet &symbol_table,
  const optionst &options,
  const std::set<irep_idt> &lib_funcs,
  message_handlert &message_handler)
{

  std::vector<irep_idt> roots;
  parse_string_list (options.get_option ("complexity-graph-roots"), roots, ",");

  std::vector<irep_idt> omitted_functions_lst;
  parse_string_list (options.get_option ("complexity-graph-omit-function"), omitted_functions_lst, ",");
  std::set<irep_idt> omitted_functions;
  for (const irep_idt &f : omitted_functions_lst)
  {
    omitted_functions.insert (f);
  }


  bool omit_function_pointers = options.get_bool_option ("complexity-graph-omit-function-pointers");

  const auto sorted = goto_functions.sorted();

  if (roots.size() == 0)
  {
    for (const auto &fun : sorted)
    {
      const auto &name = ns.lookup(fun->first).name;
      roots.push_back(name);
    }
    // could also use goto_functions.entry_point() instead
  }

  std::map<irep_idt, code_typet> type_map;
  std::unordered_set<irep_idt> address_taken;

  function_pointer_setup (symbol_table, ns, goto_functions, type_map, address_taken);

  produce_graph (symbol_table, ns, message_handler, type_map, address_taken,
                 roots, goto_functions, graph, lib_funcs,
                 omit_function_pointers, omitted_functions);

}

void compute_all_scores (
  const complexity_grapht &graph,
  const goto_functionst &goto_functions,
  const optionst &options,
  std::map<irep_idt, func_metricst> &metrics,
  std::map<irep_idt, size_t> &scores,
  std::map<irep_idt, size_t> &globalized_scores,
  const std::set<irep_idt> &lib_funcs,
  const bool use_symex_info,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
  symex_infot &max_symex_info,
  const bool use_solver_info,
  const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
  solver_infot &max_solver_info)
{

  for (const auto &it : graph.node_map)
  {
    const irep_idt &name = it.first;
    metrics.insert({name, func_metricst()});
    scores.insert({name, 1});
    globalized_scores.insert({name, 1});
  }

  // initialize scores
  compute_metrics (graph, metrics, lib_funcs,
                   use_symex_info, instr_symex_info,
                   use_solver_info, instr_solver_info);
  compute_scores (metrics, scores, use_symex_info, use_solver_info);
  if (options.get_bool_option("complexity-graph-global-scores")) 
  {
    globalize_scores (graph, scores, globalized_scores);
    normalize_scores (globalized_scores);
  }
  normalize_scores (scores);

  const auto sorted = goto_functions.sorted();

  if (use_symex_info)
  {
    for(const auto &fun : sorted)
    {
      forall_goto_program_instructions(target, fun->second.body)
      {
        const auto &symex_info = instr_symex_info.find (target);
        if (symex_info != instr_symex_info.end())
        {
          max_symex_info.duration = std::max<double>(max_symex_info.duration, symex_info->second.duration);
          max_symex_info.steps = std::max<size_t>(max_symex_info.steps, symex_info->second.steps);
        }
      }
    }
  }

  if (use_solver_info)
  {
    for(const auto &fun : sorted)
    {
      forall_goto_program_instructions(target, fun->second.body)
      {
        const auto &solver_info = instr_solver_info.find (target);
        if (solver_info != instr_solver_info.end())
        {
          max_solver_info.clauses = std::max(max_solver_info.clauses, solver_info->second.clauses);
          max_solver_info.literals = std::max(max_solver_info.literals, solver_info->second.literals);
          max_solver_info.variables = std::max(max_solver_info.variables, solver_info->second.variables);
        }
      }
    }
  }

}

// dumps the complexity graph to the output stream
void dump_complexity_graph (
  const complexity_grapht &graph,
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out,
  const optionst &options,
  const std::map<irep_idt, func_metricst> &metrics,
  const std::map<irep_idt, size_t> &scores,
  const std::map<irep_idt, size_t> &globalized_scores,
  const bool use_symex_info,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
  const symex_infot &max_symex_info,
  const bool use_solver_info,
  const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
  const solver_infot &max_solver_info)
{

  std::map<irep_idt, size_t> dot_node_naming;
  {
    size_t index = 0;
    for (const auto &it : graph.node_map)
    {
      dot_node_naming.insert ({it.first, index});
      ++index;
    }
  }

  out << "digraph G {\n\n";

  out << "rankdir=\"LR\";\n\n";

  bool include_instructions = options.get_bool_option ("complexity-graph-instructions");
  const std::map<irep_idt, size_t> &scores_to_use = options.get_bool_option ("complexity-graph-global-scores") ? globalized_scores : scores;
  dump_nodes (graph, dot_node_naming, out, include_instructions, ns, goto_functions,
              metrics, scores_to_use,
              use_symex_info, instr_symex_info, max_symex_info,
              use_solver_info, instr_solver_info, max_solver_info);

  dump_edges (graph, dot_node_naming, out, options, ns);

  out << "} // end digraph G\n";

}

void complexity_graph_main(
  const optionst &options,
  const std::string &path,
  const abstract_goto_modelt &goto_model,
  message_handlert &message_handler,
  const bool use_symex_info,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
  const bool use_solver_info,
  const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info)
{
  std::set<irep_idt> lib_funcs = {
    "strcpy", "strncpy", "__builtin___strcpy_chk",
    "strcat", "strncat", "__builtin___strcat_chk", "__builtin___strncat_chk",
    "strcmp", "strncmp", "__builtin___strncpy_chk",
    "strcasecmp", "strncasecmp",
    "strlen",
    "strdup",
    "strchr",
    "strrchr",
    "strerror",

    "memset",
    "memcpy", "__builtin___memcpy_chk",
    "memset", "__builtin_memset", "__builtin___memset_chk",
    "memmove", "__builtin___memmove_chk",
    "memcmp",

    "malloc",
    "realloc",
    "free"
  };

  const namespacet ns(goto_model.get_symbol_table());
  const goto_functionst &goto_functions = goto_model.get_goto_functions();

  complexity_grapht graph;
  construct_complexity_graph (graph, ns, goto_functions, goto_model.get_symbol_table(),
                              options, lib_funcs, message_handler);


  std::map<irep_idt, size_t> scores;
  std::map<irep_idt, size_t> globalized_scores;
  std::map<irep_idt, func_metricst> metrics;

  symex_infot max_symex_info;
  solver_infot max_solver_info;

  compute_all_scores (graph, goto_functions, options, 
                      metrics, scores, globalized_scores, 
                      lib_funcs,
                      use_symex_info, instr_symex_info, max_symex_info,
                      use_solver_info, instr_solver_info, max_solver_info);

  std::ofstream outf (path.c_str());
  std::ostream &out = outf;

  dump_complexity_graph (graph, ns, goto_functions,
                         out, options,
                         metrics, scores, globalized_scores,
                         use_symex_info, instr_symex_info, max_symex_info,
                         use_solver_info, instr_solver_info, max_solver_info);

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

  complexity_graph_main(
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
  complexity_graph_main(
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
  complexity_graph_main(
    options,
    path,
    goto_model,
    message_handler,
    use_symex_info,
    instr_symex_info,
    use_solver_info,
    instr_solver_info);
}
