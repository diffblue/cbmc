/*******************************************************************\

Module: Show the goto functions as a dot program

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Show goto functions

#include "show_complexity_graph.h"

#include <iomanip>
#include <fstream>

#include <util/ui_message.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <math.h>

#include "goto_model.h"
#include "pointer_expr.h"

#include <goto-checker/symex_coverage.h>

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

// the score metric associated with the function.
// a large score means the associated proof should be more difficult.
void compute_metrics (const symbolt &symbol, 
                      const goto_programt &goto_program, 
                      const namespacet &ns, 
                      const goto_functionst &goto_functions,
                      const bool use_symex_info,
                      const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
                      const bool use_solver_info,
                      const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
                      func_metricst &metrics) {
  metrics.indegree = indegree (symbol, ns, goto_functions);
  metrics.outdegree = outdegree (goto_program);
  metrics.num_func_pointer_calls = 0;
  metrics.function_size = function_size (goto_program);
  metrics.num_complex_ops = num_complex_ops (goto_program);
  metrics.num_loops = num_loops (goto_program);

  if (use_symex_info) {
    metrics.symex_info = aggregate_instr_info<symex_infot> (goto_program, instr_symex_info);
  }
  if (use_solver_info) {
    metrics.solver_info = aggregate_instr_info<solver_infot> (goto_program, instr_solver_info);
  }
  metrics.use_symex_info = use_symex_info;
  metrics.use_solver_info = use_solver_info;
}

void compute_metrics (const namespacet &ns, 
                      std::map<irep_idt, func_metricst> &metrics,
                      const bool use_symex_info,
                      const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
                      const bool use_solver_info,
                      const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info,
                      const goto_functionst &goto_functions) {
  const auto funs = goto_functions.sorted();

  for (const auto &fun : funs) {
    const symbolt &symbol = ns.lookup(fun->first);
    const irep_idt &name = symbol.name;
    const bool has_body = fun->second.body_available();
    if (has_body) {
      const goto_programt &body = fun->second.body;
      
      func_metricst &m = metrics.find(name)->second;
      compute_metrics (symbol, body, ns, goto_functions, 
                       use_solver_info, instr_symex_info, 
                       use_solver_info, instr_solver_info, 
                       m);
    }
  }
}

void compute_scores (std::map<irep_idt, func_metricst> &metrics,
                     std::map<irep_idt, int> &scores,
                     const bool use_symex_info,
                     const bool use_solver_info) {
  int w_indegree = 0;
  int w_outdegree = 0;
  int w_num_func_pointer_calls = 0;
  int w_function_size = 0;
  int w_num_complex_ops = 1;
  int w_num_loops = 1;
  int w_avg_time_per_symex_step = 1 ? use_symex_info : 0;

  for (auto it = metrics.begin(); it != metrics.end(); it++) {
    const irep_idt &name = it->first;
    const func_metricst &m = it->second;
    int score = w_indegree * m.indegree
              + w_outdegree * m.outdegree
              + w_num_func_pointer_calls * m.num_func_pointer_calls
              + w_function_size * m.function_size
              + w_num_complex_ops * m.num_complex_ops
              + w_num_loops * m.num_loops
              + w_avg_time_per_symex_step * (int)m.avg_time_per_symex_step()/10000;
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
    return (used != use.end() && used->second);
}

// simple depth first search
void find_used_rec (irep_idt root,
                    std::ostream &out,
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
            find_used_rec (call, out, ns, goto_functions, use);
          }
        }
      }
    }
  }
}

void find_used (irep_idt root,
                std::ostream &out,
                const namespacet &ns,
                const goto_functionst &goto_functions,
                std::map<irep_idt, bool> &use) {
  find_used_rec (root, out, ns, goto_functions, use);

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

void dump_function_call_edges 
  (const irep_idt &f,
   const goto_programt &body,
   std::ostream &out, 
   const namespacet &ns,
   std::map<irep_idt, bool> &use,
   const bool use_symex_info,
   const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info) {

  std::set<irep_idt> dont_use_calls;
  std::set<irep_idt> calls;
  std::set<std::string> func_ptrs;
  forall_goto_program_instructions(target, body) {
    if(target->is_function_call()) {
      const auto &func = target->call_function();
      if (func.id() != ID_dereference) {
        const irep_idt call = ns.lookup(to_symbol_expr(func)).name;
        if (is_used (use, call)) {
          if (use_symex_info) {
            const auto &symex_info = instr_symex_info.find(target);
            if (symex_info != instr_symex_info.end() && symex_info->second.steps != 0) {
              calls.insert (call);
            } else {
              dont_use_calls.insert (call);
            }
          } else {
            calls.insert (call);
          }
          
        }

      } else {
        const exprt &pointer = to_dereference_expr(func).pointer();

        std::stringstream stream;
        stream << "\"" << format(pointer) << "\"";

        std::string rhs = stream.str();
        func_ptrs.insert (rhs);
      }
    }
  }

  for (const auto &func_ptr : func_ptrs) {
    out << func_ptr
                 << " [" 
                 << "label=" << func_ptr << ","
                 << "shape=" << "rarrow" << ","
                 << "style=filled" << ","
                 << "fillcolor=" << "\"#" << "ffffff" << "\"" << ","
                 << "fontsize=" << 8
                 << "];\n";
  }

  for (const auto &call : calls) {
    out << normalize_name(f) << " -> " << normalize_name(call) << ";\n";
  }

  for (const auto &call : dont_use_calls) {
    std::string color = "0000ff";
    std::string opacity = "18";
    out << normalize_name(f) << " -> " << normalize_name(call)
                 << " ["
                 << "color=" << "\"#" << color << opacity << "\""
                 << "];\n";
  }

  for (const auto &func_ptr : func_ptrs) {
    out << normalize_name(f) << " -> " << func_ptr << ";\n";
  }
}


void dump_instruction 
  (const irep_idt &name,
   const goto_programt::const_targett &target,
   const int index,
   std::ostream &out,
   const namespacet &ns,
   const bool use_symex_info,
   const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info) {


  out << name << "-" << index
      << "[";

  if (use_symex_info) {
    auto symex_info = instr_symex_info.find (target);
    if (symex_info != instr_symex_info.end()) {
      // milliseconds
      double avg_time_per_step = (symex_info->second.duration / (double) symex_info->second.steps) / 1000000.0;

      int s = std::max(0, std::min (255, (int)(255 * avg_time_per_step)));
      std::string color = color_of_score (s);
      out << "fillcolor=" << "\"#" << color << "\",";
    }
  }

  out << "label=<";
  const goto_programt::instructiont &instruction = *target;
  if(instruction.is_target())
    out << std::setw(6) << instruction.target_number << ": ";
  else
    out << "        ";

  switch(instruction.type())
  {
  case NO_INSTRUCTION_TYPE:
    out << "NO INSTRUCTION TYPE SET" << '\n';
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

    out << '\n';
    break;

  case OTHER:
    if(instruction.get_other().id() == ID_code)
    {
      const auto &code = instruction.get_other();
      if(code.get_statement() == ID_array_copy)
      {
        out << "ARRAY_COPY " << format(code.op0()) << ' ' << format(code.op1())
            << '\n';
        break;
      }
      else if(code.get_statement() == ID_array_replace)
      {
        out << "ARRAY_REPLACE " << format(code.op0()) << ' '
            << format(code.op1()) << '\n';
        break;
      }
      else if(code.get_statement() == ID_array_set)
      {
        out << "ARRAY_SET " << format(code.op0()) << ' ' << format(code.op1())
            << '\n';
        break;
      }
      else if(code.get_statement() == ID_havoc_object)
      {
        out << "HAVOC_OBJECT " << format(code.op0()) << '\n';
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
        out << '\n';
        break;
      }
      else if(code.get_statement() == ID_input)
      {
        out << "INPUT";
        for(const auto &op : code.operands())
          out << ' ' << format(op);
        out << '\n';
        break;
      }
      else if(code.get_statement() == ID_output)
      {
        out << "OUTPUT " << format(code.op0()) << '\n';
        break;
      }
      // fallthrough
    }

    out << "OTHER " << format(instruction.get_other()) << '\n';
    break;

  case SET_RETURN_VALUE:
    out << "SET RETURN VALUE " << format(instruction.return_value()) << '\n';
    break;

  case DECL:
    out << "DECL " << format(instruction.decl_symbol()) << " : "
        << format(instruction.decl_symbol().type()) << '\n';
    break;

  case DEAD:
    out << "DEAD " << format(instruction.dead_symbol()) << '\n';
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
      out << '\n';
    }
    break;

  case ASSIGN:
    out << "ASSIGN " << format(instruction.assign_lhs())
        << " := " << format(instruction.assign_rhs()) << '\n';
    break;

  case ASSUME:
  case ASSERT:
    if(instruction.is_assume())
      out << "ASSUME ";
    else
      out << "ASSERT ";

    {
      out << format(instruction.condition());

      const irep_idt &comment = instruction.source_location().get_comment();
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
      const irept::subt &exception_list =
        instruction.code().find(ID_exception_list).get_sub();

      for(const auto &ex : exception_list)
        out << " " << ex.id();
    }

    if(instruction.code().operands().size() == 1)
      out << ": " << format(instruction.code().op0());

    out << '\n';
    break;

  case CATCH:
  {
    /*
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
    else if(instruction.code().get_statement() == ID_pop_catch)
    {
      out << "CATCH-POP";
    }
    else
    {
      UNREACHABLE;
    }
    */
    out << "CATCH";
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
  out << ">]" << ";\n";
}

void dump_instructions 
  (const irep_idt &name,
   const goto_programt &body,
   std::ostream &out,
   const namespacet &ns,
   const bool use_symex_info,
   const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info) {
  int index = 0;

  forall_goto_program_instructions(target, body) {
    dump_instruction (name, target, index, out, ns, use_symex_info, instr_symex_info);
    index++;
  }
}
                    

void dump_function
  (const irep_idt &f,
   const bool has_body,
   const goto_programt &body,
   std::ostream &out, 
   const namespacet &ns,
   std::map<irep_idt, bool> &use,
   std::map<irep_idt, func_metricst> &metrics,
   std::map<irep_idt, int> &scores,
   const bool use_symex_info,
   const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info) {
  if(has_body) {
    std::string color = color_of_score (scores.find (f)->second);

    int node_size = (8 + sqrt(metrics.find(f)->second.function_size));
    std::string shape = is_private (f) ? "ellipse" : "rect";
    func_metricst &m = metrics.find(f)->second;

    // dump the high-symex nodes
    if (use_symex_info) {
      forall_goto_program_instructions(target, body) {
        auto symex_info = instr_symex_info.find (target);
        if (symex_info != instr_symex_info.end()) {
          // milliseconds
          double avg_time_per_step = (symex_info->second.duration / (double) symex_info->second.steps) / 1000000.0;
          if (avg_time_per_step > 0.1) {
            out << "// HIGH SYMEX: num symex steps: " << avg_time_per_step << "\n";
            out << "/* "; 
            body.output_instruction(ns, f, out, *target);
            out << "*/\n";
          }
        }
      }
    }

    out << "{rank=same;\n";


    out << normalize_name (f)
                 << " [" 
                 << "label=" << "<" << normalize_name (f) << " <br/> ";

    m.dump_html (out);
    out << ">" << ","
                 << "shape=" << shape << ","
                 << "style=filled,"
                 << "fillcolor=" << "\"#" << color << "\","
                 << "fontsize=" << node_size
                 << "];\n";

    dump_instructions(f, body, out, ns, use_symex_info, instr_symex_info);
    out << "}\n";

    dump_function_call_edges (f, body, out, ns, use, use_symex_info, instr_symex_info);

    // fun->second.body.output(ns, f, out);
    // out << ostream::eom;
  } else {
    out << normalize_name (f)
                 << " [" 
                 << "label=" << normalize_name (f) << ","
                 << "shape=Mdiamond"
                 << "];\n";

  }
}

void dump_complexity_graph(
  const namespacet &ns,
  const std::string &path,
  const std::list<std::string> roots,
  const goto_functionst &goto_functions,
  const bool use_symex_info,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
  const bool use_solver_info,
  const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info)
{

  //goto_functionst goto_functions;
  //goto_functions.copy_from(goto_functions_);

  // ostream out(ui_message_handler);
  std::ofstream outf (path.c_str()); 
  std::ostream &out = outf;

  std::map<irep_idt, bool> use;
  if (roots.size() == 0) {
    find_used (goto_functions.entry_point(), out, ns, goto_functions, use);
  }
  for (const auto &root : roots) {
    const irep_idt &iden = root;
    find_used (iden, out, ns, goto_functions, use);
  }

  const auto sorted = goto_functions.sorted();

  // remove_functions_no_body(ns, goto_functions, use);

  // FIXME: temp
  for (const auto &fun : sorted) {
    const auto &name = ns.lookup(fun->first).name;
    const std::string str (name.c_str(), name.size());
    if (str == "s2n_calculate_stacktrace"
        || str == "s2n_result_is_ok") {
      auto it = use.find (name);
      if (it == use.end()) {
        use.insert({name, false});
      } else {
        it->second = false;
      }
    }
  }

  out << "digraph G {\n\n";
  out << "// roots: [";
  for (const auto &root : roots) {
    const irep_idt &iden = root;
    out << " " << iden;
  }
  out << "]\n";
  out << "rankdir=\"LR\";\n";

  std::map<irep_idt, int> scores;
  std::map<irep_idt, func_metricst> metrics;
  for (const auto &fun : sorted) {
    func_metricst m;
    const auto &name = ns.lookup(fun->first).name;
    metrics.insert({name, m});
    scores.insert({name, 0});
  }
  // initialize scores
  compute_metrics (ns, metrics, 
                   use_symex_info, instr_symex_info, 
                   use_solver_info, instr_solver_info, 
                   goto_functions);
  compute_scores(metrics, scores, use_symex_info, use_solver_info);

  // std::map<goto_programt::const_targett, int> test;
  // test.insert ({target, 0})
  
  //for (const auto &target : instr_dont_use) {
  //  if(target->is_function_call()) {
  //    const auto &func = target->call_function();
  //    if (func.id() != ID_dereference) {
  //      const irep_idt call = ns.lookup(to_symbol_expr(func)).name;
  //      out << "dont use: " << call << "\n";
  //    } else {
  //      out << "whoops" << "\n";
  //    }
  //  } else {
  //    out << "whoops" << "\n";
  //  }
  //  
  //}

  for(const auto &fun : sorted)
  {
    const symbolt &f_symbol = ns.lookup(fun->first);
    const bool has_body = fun->second.body_available();
    if (is_used (use, f_symbol.name)) {
      out << "\n// ------------------------------------\n\n";
      out << "//" << f_symbol.display_name()
          << " ( " << f_symbol.name << " )\n";
      dump_function (f_symbol.name, has_body, fun->second.body, out, ns, use, metrics, scores, use_symex_info, instr_symex_info);
    }
  }

  out << "} // end digraph G\n";

}


void show_complexity_graph(
  const abstract_goto_modelt &goto_model,
  const std::list<std::string> roots,
  const std::string &path)
{
  const std::map<goto_programt::const_targett, symex_infot> instr_symex_info;
  const bool use_symex_info = false;
  const std::map<goto_programt::const_targett, solver_infot> instr_solver_info;
  const bool use_solver_info = false;

  const namespacet ns(goto_model.get_symbol_table());
  dump_complexity_graph(
    ns, path,
    roots, 
    goto_model.get_goto_functions(), 
    use_symex_info,
    instr_symex_info,
    use_solver_info,
    instr_solver_info);
}
  
void show_complexity_graph(
  const abstract_goto_modelt &goto_model,
  const std::list<std::string> roots,
  const std::string &path,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info)
{
  const bool use_symex_info = true;
  const std::map<goto_programt::const_targett, solver_infot> instr_solver_info;
  const bool use_solver_info = false;
  const namespacet ns(goto_model.get_symbol_table());
  dump_complexity_graph(
    ns, path,
    roots, 
    goto_model.get_goto_functions(), 
    use_symex_info,
    instr_symex_info,
    use_solver_info,
    instr_solver_info);
}
  
void show_complexity_graph(
  const abstract_goto_modelt &goto_model,
  const std::list<std::string> roots,
  const std::string &path,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
  const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info)
{
  const bool use_symex_info = true;
  const bool use_solver_info = true;
  const namespacet ns(goto_model.get_symbol_table());
  dump_complexity_graph(
    ns, path,
    roots, 
    goto_model.get_goto_functions(), 
    use_symex_info,
    instr_symex_info,
    use_solver_info,
    instr_solver_info);
}
  

  
