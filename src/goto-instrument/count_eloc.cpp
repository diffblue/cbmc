/*******************************************************************\

Module: Count effective lines of code

Author: Michael Tautschnig

Date: December 2012

\*******************************************************************/

/// \file
/// Count effective lines of code

#include "count_eloc.h"

#include <iostream>
#include <unordered_set>

#include <util/file_util.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>

#include <goto-programs/cfg.h>
#include <goto-programs/goto_model.h>

#include <linking/static_lifetime_init.h>

typedef std::unordered_set<irep_idt> linest;
typedef std::unordered_map<irep_idt, linest> filest;
typedef std::unordered_map<irep_idt, filest> working_dirst;

static void collect_eloc(
  const goto_modelt &goto_model,
  working_dirst &dest)
{
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    forall_goto_program_instructions(it, f_it->second.body)
    {
      filest &files=dest[it->source_location.get_working_directory()];
      const irep_idt &file=it->source_location.get_file();

      if(!file.empty() &&
         !it->source_location.is_built_in())
        files[file].insert(it->source_location.get_line());
    }
  }
}

void count_eloc(const goto_modelt &goto_model)
{
  std::size_t eloc=0;

  working_dirst eloc_map;
  collect_eloc(goto_model, eloc_map);

  for(const std::pair<irep_idt, filest> &files : eloc_map)
    for(const std::pair<irep_idt, linest> &lines : files.second)
      eloc+=lines.second.size();

  std::cout << "Effective lines of code: " << eloc << '\n';
}

void list_eloc(const goto_modelt &goto_model)
{
  working_dirst eloc_map;
  collect_eloc(goto_model, eloc_map);

  for(const std::pair<irep_idt, filest> &files : eloc_map)
    for(const std::pair<irep_idt, linest> &lines : files.second)
    {
      std::string file=id2string(lines.first);
      if(!files.first.empty())
        file=concat_dir_file(id2string(files.first), file);

      for(const irep_idt &line : lines.second)
        std::cout << file << ':' << line << '\n';
    }
}

void print_path_lengths(const goto_modelt &goto_model)
{
  const irep_idt &entry_point=goto_model.goto_functions.entry_point();
  goto_functionst::function_mapt::const_iterator start=
    goto_model.goto_functions.function_map.find(entry_point);

  if(start==goto_model.goto_functions.function_map.end() ||
     !start->second.body_available())
  {
    std::cout << "No entry point found, path length undefined\n";
    return;
  }

  struct visited_cfg_nodet
  {
    bool visited;

    visited_cfg_nodet():visited(false)
    {
    }
  };

  typedef cfg_baset<visited_cfg_nodet> cfgt;
  cfgt cfg;
  cfg(goto_model.goto_functions);

  const goto_programt &start_program=start->second.body;

  const cfgt::entryt &start_node=
    cfg.entry_map[start_program.instructions.begin()];
  const cfgt::entryt &last_node=
    cfg.entry_map[--start_program.instructions.end()];

  cfgt::patht shortest_path;
  cfg.shortest_path(start_node, last_node, shortest_path);
  std::cout << "Shortest control-flow path: " << shortest_path.size()
            << " instructions\n";

  std::size_t n_loops=0, loop_ins=0;
  forall_goto_functions(gf_it, goto_model.goto_functions)
    forall_goto_program_instructions(i_it, gf_it->second.body)
      // loops or recursion
      if(i_it->is_backwards_goto() ||
         i_it==gf_it->second.body.instructions.begin())
      {
        const cfgt::entryt &node=cfg.entry_map[i_it];
        cfgt::patht loop;
        cfg.shortest_loop(node, loop);

        if(!loop.empty())
        {
          ++n_loops;
          loop_ins+=loop.size()-1;
        }
      }

  if(n_loops>0)
    std::cout << "Loop information: " << n_loops << " loops, "
              << loop_ins << " instructions in shortest paths of loop bodies\n";

  std::size_t n_reachable=0;
  cfg.visit_reachable(start_node);
  for(std::size_t i=0; i<cfg.size(); ++i)
    if(cfg[i].visited)
      ++n_reachable;
  std::cout << "Reachable instructions: " << n_reachable << "\n";
}

void print_global_state_size(const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  // if we have a linked object, only account for those that are used
  // (slice-global-inits may have been used to avoid unnecessary initialization)
  goto_functionst::function_mapt::const_iterator f_it =
    goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
  const bool has_initialize =
    f_it != goto_model.goto_functions.function_map.end();
  std::unordered_set<irep_idt> initialized;

  if(has_initialize)
  {
    for(const auto &ins : f_it->second.body.instructions)
    {
      if(ins.is_assign())
      {
        const code_assignt &code_assign = to_code_assign(ins.code);
        object_descriptor_exprt ode;
        ode.build(code_assign.lhs(), ns);

        if(ode.root_object().id() == ID_symbol)
        {
          const symbol_exprt &symbol_expr = to_symbol_expr(ode.root_object());
          initialized.insert(symbol_expr.get_identifier());
        }
      }
    }
  }

  mp_integer total_size = 0;

  for(const auto &symbol_entry : goto_model.symbol_table.symbols)
  {
    const symbolt &symbol = symbol_entry.second;
    if(
      symbol.is_type || symbol.is_macro || symbol.type.id() == ID_code ||
      symbol.type.get_bool(ID_C_constant) ||
      has_prefix(id2string(symbol.name), CPROVER_PREFIX) ||
      (has_initialize && initialized.find(symbol.name) == initialized.end()))
    {
      continue;
    }

    const auto bits = pointer_offset_bits(symbol.type, ns);
    if(bits.has_value() && bits.value() > 0)
      total_size += bits.value();
  }

  std::cout << "Total size of global objects: " << total_size << " bits\n";
}
