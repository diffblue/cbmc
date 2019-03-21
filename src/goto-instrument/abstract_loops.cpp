/*******************************************************************\

Module: Loop shrinking

Author: Zhixing Xu, zhixingx@princeton.edu

\*******************************************************************/

#include "abstract_loops.h"

#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/std_expr.h>
#include <util/string2int.h>
#include <util/string_utils.h>

#include <analyses/dependence_graph.h>
#include <analyses/goto_rw.h>
#include <analyses/natural_loops.h>

#include <goto-programs/cfg.h>
#include <goto-programs/remove_skip.h>

// #define DEBUG_ABSTRACT_LOOPS

#ifdef DEBUG_ABSTRACT_LOOPS
#include <iostream>
#endif

#include <iterator>

class abstract_loopst
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;

  abstract_loopst(goto_modelt &goto_model, const loop_mapt &_target_loop_map)
    : target_loop_map(_target_loop_map), ns(goto_model.symbol_table)
  {
    // compute program dependence graph
    dependence_grapht dep_graph(ns);
    // data structures initialization
    dep_graph(goto_model.goto_functions, ns);

    // map location numbers to function identifiers as the dependence graph does
    // not provide a mapping from program counters to the function containing
    // the instruction
    for(const auto &gf_entry : goto_model.goto_functions.function_map)
    {
      for(const auto &instruction : gf_entry.second.body.instructions)
        location_to_function[instruction.location_number] = gf_entry.first;
    }

    // build the CFG data structure
    cfg(goto_model.goto_functions);
    // call main function
    abstract_loops(goto_model, dep_graph);
  }

protected:
  // target abstract loop number for each function
  const loop_mapt &target_loop_map;
  // map from location number to the set of loops it belongs to
  typedef std::set<unsigned> nodeset;
  std::map<unsigned, nodeset> insloop_map;
  // set of instructions in loop
  typedef const natural_loops_mutablet::natural_loopt loopt;
  // data dependency set
  typedef dep_graph_domaint::depst depst;
  // map location numbers to function identifiers
  std::map<unsigned, irep_idt> location_to_function;
  // name space for program
  const namespacet ns;
  // cfg
  struct cfg_nodet
  {
    cfg_nodet() : node_required(false)
    {
    }

    bool node_required;
  };

  typedef cfg_baset<cfg_nodet> cfgt;
  cfgt cfg;

  void
  abstract_loops(goto_modelt &goto_model, const dependence_grapht &dep_graph);

  void get_loop_info(
    const irep_idt &function_id,
    const loopt &,
    const dependence_grapht &dep_graph);

  void update_shrinkability(unsigned loc, const irep_idt &function_id);

  void check_assertion(
    unsigned location,
    const dependence_grapht &dep_graph,
    const goto_functionst &goto_functions);

  void abstract_goto_program(
    const irep_idt &function_id,
    unsigned loop_num,
    const dependence_grapht &dep_graph,
    goto_functionst &goto_functions);

  /// add an element to unique queue
  /// \param s: set to keep queue elements unique
  /// \param q: the queue
  /// \param e: element add to queue
  void add_to_queue(nodeset &s, std::queue<unsigned> &q, unsigned e)
  {
    if(s.insert(e).second)
      q.push(e);
  }

  /// Check if the loop is a target for shrinking
  /// \param function_id: function to contain loop
  /// \param loop_num: loop_number to check
  /// \return: true if the loop is shrinking target
  bool check_target(const irep_idt &function_id, unsigned loop_num) const
  {
    auto function_entry = target_loop_map.find(function_id);
    return target_loop_map.empty() ||
           (function_entry != target_loop_map.end() &&
            function_entry->second.find(loop_num) !=
              function_entry->second.end());
  }

  /// Check if a node has self-cycle in data dependency
  /// Inefficient method, should get updated
  /// \param target: node location
  /// \param dep_graph: dependency graph for the program
  bool is_in_cycle(unsigned target, const dependence_grapht &dep_graph)
  {
    nodeset dep_set;
    std::queue<unsigned> dep_queue;

    depst data_deps = dep_graph[dep_graph[target].PC].get_data_deps();

    for(const auto &dep : data_deps)
      add_to_queue(dep_set, dep_queue, dep->location_number);

    while(!dep_queue.empty())
    {
      unsigned node = dep_queue.front();
      if(node == target)
        return true;

      dep_queue.pop();
      data_deps = dep_graph[dep_graph[node].PC].get_data_deps();

      for(const auto &dep : data_deps)
        add_to_queue(dep_set, dep_queue, dep->location_number);
    }

    return false;
  }

  // class to keep information of a single loop with simple helper function
  class abstract_loopt
  {
  public:
    abstract_loopt(
      goto_programt::targett _head,
      goto_programt::targett _tail,
      irep_idt _loop_var)
      : head(_head), tail(_tail), loop_var(_loop_var), shrinkable(true)
    {
    }

    // Loop variable dependency leaves
    nodeset var_leaves;
    // lines update loop variable value
    nodeset var_updates;
    // loop head and tail
    goto_programt::targett head;
    goto_programt::targett tail;
    // Loop variable
    irep_idt loop_var;
    // loop variable initialization location
    unsigned init_loc;
    // loop shrinkable or not
    bool shrinkable;

    /// make loop head an assumption(constraint) for loop variable
    /// skip the goto at loop end
    void build_assumption()
    {
      // make the goto inst into an assumption
      head->make_assumption(boolean_negate(head->guard));
      // skip loop end line
      tail->turn_into_skip();
    }
  };

  // map from the function name to loop information map
  typedef std::map<unsigned, abstract_loopt> loopnum_mapt;
  std::map<irep_idt, loopnum_mapt> absloop_map;

#ifdef DEBUG_ABSTRACT_LOOPS
  /// print out nodes in set
  static void print_nodes(abstract_loopst::nodeset &node_set)
  {
    for(abstract_loopst::nodeset::iterator it = node_set.begin();
        it != node_set.end();
        ++it)
    {
      if(it != node_set.begin())
        std::cout << ",";
      std::cout << *it;
    }
    std::cout << '\n';
  }
#endif
}; // end of class abstract_loopst

/// Do the abstraction on goto program (modify goto program)
/// \param function_id: identifier of function containing loop
/// \param loop_num: target loop number
/// \param dep_graph: dependency graph for the program
/// \param goto_functions: goto_functions to abstract
void abstract_loopst::abstract_goto_program(
  const irep_idt &function_id,
  unsigned loop_num,
  const dependence_grapht &dep_graph,
  goto_functionst &goto_functions)
{
  abstract_loopt *loop_info =
    &(absloop_map[function_id].find(loop_num)->second);

#ifdef DEBUG_ABSTRACT_LOOPS
  std::cout << "==Shrink loop #" << loop_num << " in " << function_id << "\n";
#endif

  unsigned update_loc = *(loop_info->var_updates.begin());
  bool is_inc = true;
  goto_functionst::function_mapt::iterator f_it =
    goto_functions.function_map.find(
      location_to_function.at(dep_graph[update_loc].PC->location_number));
  CHECK_RETURN(!f_it->second.body.instructions.empty());
  goto_programt::targett i_it = f_it->second.body.instructions.begin();
  std::advance(i_it, update_loc - i_it->location_number);

  INVARIANT(i_it->is_assign(), "instruction should be an assignment");
  exprt expr = to_code_assign(i_it->code).rhs();
  // This assumes loop variable is updated by +/-
  if(expr.id() == ID_plus)
    is_inc = true;
  else if(expr.id() == ID_minus)
    is_inc = false;
  else // do not do abstraction
  {
#ifdef DEBUG_ABSTRACT_LOOPS
    std::cout << "Unshrinkable: Loop variable change not by +/-\n";
#endif
    return;
  }
  // skip variable update line
  i_it->make_skip();

  // change the initial assignment into assumption
  f_it = goto_functions.function_map.find(function_id);
  i_it = f_it->second.body.instructions.begin();
  std::advance(i_it, loop_info->init_loc - i_it->location_number);
  expr = i_it->code;
  expr.id(is_inc ? ID_ge : ID_le);
  expr.type().id(ID_bool);
  i_it->make_assumption(expr);

  // change loop head into assumption, skip goto at loop end
  loop_info->build_assumption();
}

/// Mark all loops containing the assignment unshrinkable
/// \param loc: location number
/// \param function_id: function containing the instruction
void abstract_loopst::update_shrinkability(
  unsigned loc,
  const irep_idt &function_id)
{
  for(auto loop_n : insloop_map[loc])
  {
    abstract_loopt *loop_info =
      &(absloop_map[function_id].find(loop_n)->second);
    loop_info->shrinkable = false;
#ifdef DEBUG_ABSTRACT_LOOPS
    std::cout << " - intermediate node " << loc << " makes " << function_id
              << "::" << loop_n << " unshrinkable\n";
#endif
  }
}

/// Check data dependency for all assertions
/// \param location: line number for assertion
/// \param dep_graph: dependency graph for the program
/// \param goto_functions: source goto functions
void abstract_loopst::check_assertion(
  unsigned location,
  const dependence_grapht &dep_graph,
  const goto_functionst &goto_functions)
{
#ifdef DEBUG_ABSTRACT_LOOPS
  std::cout << "Check assertion at: " << location << "\n";
#endif
  nodeset leaf_set, update_set;

  goto_programt::const_targett i_it = dep_graph[location].PC;
  depst data_deps = dep_graph[i_it].get_data_deps();
  depst control_deps = dep_graph[i_it].get_control_deps();
  nodeset dep_set, ctrl_set;
  std::queue<unsigned> dep_queue;

  for(const auto &dep : data_deps)
    add_to_queue(dep_set, dep_queue, dep->location_number);

  for(const auto &cdep : control_deps)
  {
    add_to_queue(dep_set, dep_queue, cdep->location_number);
    ctrl_set.insert(cdep->location_number);
  }

  while(!dep_queue.empty())
  {
    unsigned node = dep_queue.front();
    dep_queue.pop();
    data_deps = dep_graph[dep_graph[node].PC].get_data_deps();
    control_deps = dep_graph[dep_graph[node].PC].get_control_deps();
    if(!data_deps.empty())
    {
      for(const auto &dep : data_deps)
      {
        add_to_queue(dep_set, dep_queue, dep->location_number);
        if(ctrl_set.find(node) == ctrl_set.end())
          update_set.insert(node);
      }
    }
    else
      leaf_set.insert(node);

    for(const auto &cdep : control_deps)
    {
      add_to_queue(dep_set, dep_queue, cdep->location_number);
      ctrl_set.insert(cdep->location_number);
    }
  }
#ifdef DEBUG_ABSTRACT_LOOPS
  std::cout << "  Leaf dependency nodes: ";
  print_nodes(leaf_set);
  std::cout << "  Update node: ";
  print_nodes(update_set);
#endif

  // node set
  nodeset leaf_nodes;
  nodeset update_nodes;
  for(auto loop_n : insloop_map[location])
  {
    irep_idt func =
      location_to_function.at(dep_graph[location].PC->location_number);
    abstract_loopt *loop_info = &(absloop_map[func].find(loop_n)->second);
    leaf_nodes.insert(
      loop_info->var_leaves.begin(), loop_info->var_leaves.end());
    update_nodes.insert(
      loop_info->var_updates.begin(), loop_info->var_updates.end());
  }
  // check dependence of leaf set
  nodeset diff;
  std::set_difference(
    leaf_set.begin(),
    leaf_set.end(),
    leaf_nodes.begin(),
    leaf_nodes.end(),
    std::inserter(diff, diff.begin()));
  // loops containing the update nodes should not be shrinkable
  for(auto loc : diff)
  {
    update_shrinkability(
      loc, location_to_function.at(dep_graph[loc].PC->location_number));
  }

  // check dependence of update set
  diff.clear();
  std::set_difference(
    update_set.begin(),
    update_set.end(),
    update_nodes.begin(),
    update_nodes.end(),
    std::inserter(diff, diff.begin()));
  // loops containing the update nodes should not be shrinkable
  for(auto loc : diff)
  {
    if(is_in_cycle(loc, dep_graph))
    {
      nodeset entry_set;
      std::queue<unsigned> entry_queue;
      add_to_queue(entry_set, entry_queue, loc);
      while(!entry_queue.empty())
      {
        unsigned node = entry_queue.front();
        entry_queue.pop();
        const irep_idt &function_id =
          location_to_function.at(dep_graph[node].PC->location_number);
        update_shrinkability(node, function_id);
        // check loops calling this function
        goto_functionst::function_mapt::const_iterator f_it =
          goto_functions.function_map.find(function_id);
        CHECK_RETURN(f_it != goto_functions.function_map.end());

        goto_programt::const_targett begin_function =
          f_it->second.body.instructions.begin();

        cfgt::entry_mapt::const_iterator entry =
          cfg.entry_map.find(begin_function);
        if(entry != cfg.entry_map.end())
        {
          for(const auto &edge : cfg[entry->second].in)
            add_to_queue(entry_set, entry_queue, edge.first);
        }
      }
    }
    else
    {
      // check if the update depends on loop variable
      const goto_programt::instructiont &inst = *(dep_graph[loc].PC);
      if(!inst.is_assign())
        continue;
      value_setst &value_sets =
        dep_graph.reaching_definitions().get_value_sets();
      rw_range_set_value_sett rw_set(ns, value_sets);
      const code_assignt &code_assign = to_code_assign(inst.code);
      rw_set.get_objects_rec(
        location_to_function.at(dep_graph[loc].PC->location_number),
        dep_graph[loc].PC,
        rw_range_sett::get_modet::READ,
        code_assign.lhs());
      bool dep_on_loop_var = false;
      for(auto loop_n : insloop_map[loc])
      {
        const irep_idt &func =
          location_to_function.at(dep_graph[loc].PC->location_number);
        abstract_loopt *loop_info = &(absloop_map[func].find(loop_n)->second);
        if(
          rw_set.get_r_set().find(loop_info->loop_var) !=
          rw_set.get_r_set().end())
        {
          dep_on_loop_var = true;
        }
      }
      if(dep_on_loop_var)
      {
        update_shrinkability(
          loc, location_to_function.at(dep_graph[loc].PC->location_number));
      }
    }
  }
}

/// Get loop information, create class to store the info
/// \param function_id: Name of the function the loop is part of
/// \param loop: list of instructions in loop
/// \param dep_graph: dependency graph for the program
void abstract_loopst::get_loop_info(
  const irep_idt &function_id,
  const loopt &loop,
  const dependence_grapht &dep_graph)
{
  PRECONDITION(!loop.empty());

  // construct loop map, make instructions ordered
  std::map<unsigned, goto_programt::targett> loop_map;
  for(loopt::const_iterator l_it = loop.begin(); l_it != loop.end(); l_it++)
    loop_map[(*l_it)->location_number] = *l_it;

  goto_programt::targett head = loop_map.begin()->second;
  goto_programt::targett last = (--loop_map.end())->second;
  CHECK_RETURN(last->is_backwards_goto());

#ifdef DEBUG_ABSTRACT_LOOPS
  std::cout << "Loop " << function_id << "::" << last->loop_number
            << "\n- head location: " << head->location_number << "\n";
#endif

  // Only deal with loops starting with goto instruction
  if(!head->is_goto())
  {
#ifdef DEBUG_ABSTRACT_LOOPS
    std::cout << "Unshrinkable: only deal with loop start with goto\n";
#endif
    return;
  }

  // identify loop variable
  value_setst &value_sets = dep_graph.reaching_definitions().get_value_sets();
  rw_range_set_value_sett rw_set(ns, value_sets);
  goto_rw(function_id, head, rw_set);
  // can only handle single loop guard with one symbol now
  if(rw_set.get_r_set().size() != 1)
  {
    // do nothing, won't record information of this loop
#ifdef DEBUG_ABSTRACT_LOOPS
    std::cout << "Unshrinkable: loop condition with multiple variable\n";
#endif
    return;
  }
  irep_idt loop_var = rw_set.get_r_set().begin()->first;
#ifdef DEBUG_ABSTRACT_LOOPS
  std::cout << "- loop variable: " << loop_var << "\n";
#endif

  abstract_loopt loop_info(head, last, loop_var);

  // find dependence nodes for the loop variable
  depst data_deps = dep_graph[head].get_data_deps();
  nodeset dep_set, direct_dep;
  std::queue<unsigned> dep_queue;

  for(const auto &dep : data_deps)
  {
    add_to_queue(dep_set, dep_queue, dep->location_number);
    direct_dep.insert(dep->location_number);
  }

  while(!dep_queue.empty())
  {
    unsigned node = dep_queue.front();
    dep_queue.pop();
    data_deps = dep_graph[dep_graph[node].PC].get_data_deps();
    if(!data_deps.empty())
    {
      for(const auto &dep : data_deps)
      {
        add_to_queue(dep_set, dep_queue, dep->location_number);
        if(is_in_cycle(node, dep_graph))
          loop_info.var_updates.insert(node);
      }
    }
    else
      loop_info.var_leaves.insert(node);
  }

  // Only handle loops with simple loop variable initialization and update
  // TODO: handle situation where loop variable is updated multiple times
  if(loop_info.var_updates.size() != 1)
  {
#ifdef DEBUG_ABSTRACT_LOOPS
    std::cout << "Unshrinkable: Loop variable has multiple/no update\n";
#endif
    return;
  }
  // get loop variable initialization location
  nodeset diff;
  std::set_difference(
    direct_dep.begin(),
    direct_dep.end(),
    loop_info.var_updates.begin(),
    loop_info.var_updates.end(),
    std::inserter(diff, diff.begin()));
  if(diff.size() == 1)
    loop_info.init_loc = *(diff.begin());
  else
  {
#ifdef DEBUG_ABSTRACT_LOOPS
    std::cout << "Unshrinkable: Loop variable has no/multiple init\n";
#endif
    return;
  }

  // This is for SVcomp cases where values can be nondet
  const code_assignt &code_assign =
    to_code_assign(dep_graph[loop_info.init_loc].PC->code);
  if(code_assign.rhs().id() == ID_side_effect)
  {
#ifdef DEBUG_ABSTRACT_LOOPS
    std::cout << "Unshrinkable: Loop variable init to nondet\n";
#endif
    return;
  }

#ifdef DEBUG_ABSTRACT_LOOPS
  std::cout << "  Leaf dependency nodes for loop variable: ";
  print_nodes(loop_info.var_leaves);
  std::cout << "  Update node for loop variable: ";
  print_nodes(loop_info.var_updates);
#endif

  // add to the instruction # -> loop # map
  // unsafe with function call, further check when doing abstraction
  for(unsigned n = head->location_number; n <= last->location_number; n++)
    insloop_map[n].insert(last->loop_number);

  absloop_map[function_id].emplace(last->loop_number, loop_info);
}

/// Main function for abstraction, has 3 iterations to
/// 1. Identify loop variables and their dependency
/// 2. Check assertions in program and their dependency
/// 3. Abstract shrinkable loop in goto program
/// \param goto_model: input goto model to modify
/// \param dep_graph: dependency graph for the program
void abstract_loopst::abstract_loops(
  goto_modelt &goto_model,
  const dependence_grapht &dep_graph)
{
  // iter over loops to identify all loop variables and their dependence
  Forall_goto_functions(it, goto_model.goto_functions)
  {
    if(!it->second.body_available())
      continue;

    natural_loops_mutablet natural_loops((it->second).body);
    for(const auto &loop : natural_loops.loop_map)
      get_loop_info(it->first, loop.second, dep_graph);
  }

  // iter over all assertions to check their dependence
  Forall_goto_functions(it, goto_model.goto_functions)
  {
    if(!it->second.body_available())
      continue;

    Forall_goto_program_instructions(i_it, it->second.body)
    {
      if(i_it->is_assert())
      {
        check_assertion(
          i_it->location_number, dep_graph, goto_model.goto_functions);
      }
    }
  }

  // abstract the shrinkable loops
  for(const auto &abstraction_entry : absloop_map)
  {
    const irep_idt &function_id = abstraction_entry.first;

    for(const auto &loop_entry : abstraction_entry.second)
    {
      if(
        loop_entry.second.shrinkable &&
        check_target(function_id, loop_entry.first))
      {
        abstract_goto_program(
          function_id, loop_entry.first, dep_graph, goto_model.goto_functions);
      }
    }
  }
}

/// Create abstract_loopst struct for given goto program
/// \param goto_model: the goto progarm model
/// \param target_loop_map: the target_loops to shrink
void abstract_loops(goto_modelt &goto_model, const loop_mapt &target_loop_map)
{
  abstract_loopst(goto_model, target_loop_map);
  remove_skip(goto_model);
}

/// Parse input of target loops.
/// Similar to the function with same name in skip_loops.cpp
/// \param loop_ids: input string of target loop
/// \param [out] funcloop_map: a map from function name to loop number
/// \return return false if parse succeeds
static bool parse_loop_ids(const std::string &loop_ids, loop_mapt &funcloop_map)
{
  std::vector<std::string> loops;
  split_string(loop_ids, ',', loops, true, true);

  for(const auto &loop : loops)
  {
    std::string::size_type delim = loop.rfind(".");

    if(delim == std::string::npos)
      return true;

    const std::string function_id = loop.substr(0, delim);
    const unsigned nr = safe_string2unsigned(loop.substr(delim + 1));

    funcloop_map[function_id].insert(nr);
  }

  return false;
}

bool parse_absloopset(const std::string &inputset, loop_mapt &target_loop_map)
{
  return parse_loop_ids(inputset, target_loop_map);
}
