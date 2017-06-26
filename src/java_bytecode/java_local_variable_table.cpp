/*******************************************************************\

Module: Java local variable table processing

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Java local variable table processing

#include "java_bytecode_convert_method_class.h"

#include "java_types.h"
#include "java_utils.h"

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/string2int.h>

#include <climits>
#include <iostream>

// Specialise the CFG representation to work over Java instead of GOTO programs.
// This must be done at global scope due to template resolution rules.

template<class T>
struct procedure_local_cfg_baset<
  T,
  java_bytecode_convert_methodt::method_with_amapt,
  unsigned> :
  public grapht<cfg_base_nodet<T, unsigned> >
{
  typedef java_bytecode_convert_methodt::method_with_amapt method_with_amapt;
  typedef std::map<unsigned, unsigned> entry_mapt;
  entry_mapt entry_map;

  procedure_local_cfg_baset() {}

  void operator()(const method_with_amapt &args)
  {
    const auto &method=args.first;
    const auto &amap=args.second;
    for(const auto &inst : amap)
    {
      // Map instruction PCs onto node indices:
      entry_map[inst.first]=this->add_node();
      // Map back:
      (*this)[entry_map[inst.first]].PC=inst.first;
    }
    // Add edges declared in the address map:
    for(const auto &inst : amap)
    {
      for(auto succ : inst.second.successors)
        this->add_edge(entry_map.at(inst.first), entry_map.at(succ));
    }
    // Next, add edges declared in the exception table, which
    // don't figure in the address map successors/predecessors as yet:
    for(const auto &table_entry : method.exception_table)
    {
      auto findit=amap.find(table_entry.start_pc);
      INVARIANT(findit!=amap.end(),
             "Exception table entry doesn't point to an instruction?");
      for(; findit->first<table_entry.end_pc; ++findit)
      {
        // For now just assume any non-branch
        // instruction could potentially throw.
        auto succit=findit;
        ++succit;
        if(succit==amap.end())
          continue;
        const auto &thisinst=findit->second;
        if(thisinst.successors.size()==1 &&
           thisinst.successors.back()==succit->first)
        {
          this->add_edge(
            entry_map.at(findit->first),
            entry_map.at(table_entry.handler_pc));
        }
      }
    }
  }

  unsigned get_first_node(const method_with_amapt &args) const
  {
    return args.second.begin()->first;
  }
  unsigned get_last_node(const method_with_amapt &args) const
  {
    return (--args.second.end())->first;
  }
  unsigned nodes_empty(const method_with_amapt &args) const
  {
    return args.second.empty();
  }
};

// Grab some class typedefs for brevity:
typedef java_bytecode_convert_methodt::holet
  holet;
typedef java_bytecode_convert_methodt::local_variable_with_holest
  local_variable_with_holest;
typedef java_bytecode_convert_methodt::local_variable_table_with_holest
  local_variable_table_with_holest;
typedef java_bytecode_convert_methodt::address_mapt
  address_mapt;
typedef java_bytecode_convert_methodt::java_cfg_dominatorst
  java_cfg_dominatorst;

// Comparators for local variables:

static bool lt_index(
  const local_variable_with_holest &a,
  const local_variable_with_holest &b)
{
  return a.var.index<b.var.index;
}
static bool lt_startpc(
  const local_variable_with_holest *a,
  const local_variable_with_holest *b)
{
  return a->var.start_pc<b->var.start_pc;
}

// The predecessor map, and a top-sorting comparator:

typedef std::map<
  local_variable_with_holest *,
  std::set<local_variable_with_holest *> >
  predecessor_mapt;

struct is_predecessor_oft
{
  const predecessor_mapt &order;

  explicit is_predecessor_oft(const predecessor_mapt &_order) : order(_order) {}

  bool operator()(
    local_variable_with_holest *a,
    local_variable_with_holest *b) const
  {
    auto findit=order.find(a);
    if(findit==order.end())
      return false;
    return findit->second.count(b)>0;
  }
};

// Helper routines for the find-initialisers code below:

/// See above
/// `start`: Variable to find the predecessors of `predecessor_map`: Map from
///   local variables to sets of predecessors
/// \param Outputs: `result`: populated with all transitive predecessors of
///   `start` found in `predecessor_map`
static void gather_transitive_predecessors(
  local_variable_with_holest *start,
  const predecessor_mapt &predecessor_map,
  std::set<local_variable_with_holest*> &result)
{
  if(!result.insert(start).second)
    return;
  auto findit=predecessor_map.find(start);
  if(findit==predecessor_map.end())
    return;
  for(const auto pred : findit->second)
    gather_transitive_predecessors(pred, predecessor_map, result);
}

/// See above
/// \par parameters: `inst`: Java bytecode instruction
/// `slotidx`: local variable slot number
/// \return Returns true if `inst` is any form of store instruction targeting
///   slot `slotidx`
static bool is_store_to_slot(
  const java_bytecode_convert_methodt::instructiont &inst,
  unsigned slotidx)
{
  const std::string prevstatement=id2string(inst.statement);
  if(!(prevstatement.size()>=1 && prevstatement.substr(1, 5)=="store"))
    return false;

  unsigned storeslotidx;
  if(inst.args.size()==1)
  {
    // Store with an argument:
    const auto &arg=inst.args[0];
    bool ret=to_unsigned_integer(to_constant_expr(arg), storeslotidx);
    CHECK_RETURN(!ret);
  }
  else
  {
    // Store shorthands, like "store_0", "store_1"
    INVARIANT(prevstatement[6]=='_' && prevstatement.size()==8,
      "expected store instruction looks like store_0, store_1...");
    storeslot=prevstatement[7];
    INVARIANT(isdigit(storeslot[0]),
      "store_? instructions should end in a digit");
    storeslotidx=safe_string2unsigned(storeslot);
  }
  return storeslotidx==slotidx;
}

/// See above
/// \par parameters: `from`, `to`: bounds of a gap in `var`'s live range,
/// inclusive and exclusive respectively
/// \return Adds a hole to `var`, unless it would be of zero size.
static void maybe_add_hole(
  local_variable_with_holest &var,
  unsigned from,
  unsigned to)
{
  PRECONDITION(to>=from);
  if(to!=from)
    var.holes.push_back({from, to-from});
}

/// See above
/// \par parameters: `firstvar`-`varlimit`: range of local variable table
/// entries to consider
/// \return `live_variable_at_address` is populated with a sequence of local
///   variable table entry pointers, such that `live_variable_at_address[addr]`
///   yields the unique table entry covering that address. Asserts if entries
///   overlap.
static void populate_variable_address_map(
  local_variable_table_with_holest::iterator firstvar,
  local_variable_table_with_holest::iterator varlimit,
  std::vector<local_variable_with_holest *> &live_variable_at_address)
{
  for(auto it=firstvar, itend=varlimit; it!=itend; ++it)
  {
    if(it->var.start_pc+it->var.length>live_variable_at_address.size())
      live_variable_at_address.resize(it->var.start_pc+it->var.length);

    for(unsigned idx=it->var.start_pc,
          idxlim=it->var.start_pc+it->var.length;
        idx!=idxlim;
        ++idx)
    {
      INVARIANT(!live_variable_at_address[idx], "Local variable table clash?");
      live_variable_at_address[idx]=&*it;
    }
  }
}

/// Usually a live variable range begins with a store instruction initialising
/// the relevant local variable slot, but instead of or in addition to this,
/// control flow edges may exist from bytecode addresses that fall under a table
/// entry which differs, but which has the same variable name and type
/// descriptor. This indicates a split live range, and will be recorded in the
/// predecessor map.
/// \par parameters: `firstvar`-`varlimit`: range of local variable table
///   entries to consider
/// `live_variable_at_address`: map from bytecode address to table entry (drawn
///   from firstvar-varlimit) live at that address
/// `amap`: map from bytecode address to instructions
/// \return Populates `predecessor_map` with a graph from local variable table
///   entries to their predecessors (table entries which may flow together and
///   thus may be considered the same live range).
static void populate_predecessor_map(
  local_variable_table_with_holest::iterator firstvar,
  local_variable_table_with_holest::iterator varlimit,
  const std::vector<local_variable_with_holest *> &live_variable_at_address,
  const address_mapt &amap,
  predecessor_mapt &predecessor_map,
  message_handlert &msg_handler)
{
  messaget msg(msg_handler);
  for(auto it=firstvar, itend=varlimit; it!=itend; ++it)
  {
    // All entries of the "local_variable_table_with_holest" processed in this
    // function concern the same Java Local Variable Table slot/register. This
    // is because "find_initialisers()" has already sorted them.
    INVARIANT(it->var.index==firstvar->var.index,
      "all entries are for the same local variable slot");

    // Parameters are irrelevant to us and shouldn't be changed. This is because
    // they cannot have live predecessor ranges: they are initialized by the JVM
    // and no other live variable range can flow into them.
    if(it->is_parameter)
      continue;

    // Find the last instruction within the live range:
    unsigned end_pc=it->var.start_pc+it->var.length;
    auto amapit=amap.find(end_pc);
    INVARIANT(amapit!=amap.begin(),
      "current bytecode shall not be the first");
    auto old_amapit=amapit;
    --amapit;
    if(old_amapit==amap.end())
    {
      INVARIANT(end_pc>amapit->first,
        "Instruction live range doesn't align to instruction boundary?");
    }

    // Find vartable entries that flow into this one:
    unsigned new_start_pc=it->var.start_pc;
    for(; amapit->first>=it->var.start_pc; --amapit)
    {
      for(auto pred : amapit->second.predecessors)
      {
        auto pred_var=
          (pred<live_variable_at_address.size() ?
           live_variable_at_address[pred] :
           nullptr);

        if(pred_var==&*it)
        {
          // Flow from within same live range?
          continue;
        }
        else if(!pred_var)
        {
          // Flow from out of range?
          // Check if this is an initialiser, and if so expand the live range
          // to include it, but don't check its predecessors:
          auto inst_before_this=amapit;
          INVARIANT(inst_before_this!=amap.begin(),
            "we shall not be on the first bytecode of the method");
          --inst_before_this;
          if(amapit->first!=it->var.start_pc || inst_before_this->first!=pred)
          {
            // These sorts of infeasible edges can occur because jsr
            // handling is presently vague (any subroutine is assumed to
            // be able to return to any callsite)
            msg.warning() << "Local variable table: ignoring flow from "
                          << "out of range for " << it->var.name << ' '
                          << pred << " -> " << amapit->first
                          << messaget::eom;
            continue;
          }
          if(!is_store_to_slot(
               *(inst_before_this->second.source),
               it->var.index))
          {
            throw "local variable table: didn't find initialising store";
          }
          new_start_pc=pred;
        }
        else
        {
          if(pred_var->var.name!=it->var.name ||
             pred_var->var.signature!=it->var.signature)
          {
            // These sorts of infeasible edges can occur because
            // jsr handling is presently vague (any subroutine is
            // assumed to be able to return to any callsite)
            msg.warning() << "Local variable table: ignoring flow from "
                          << "clashing variable for "
                          << it->var.name << ' ' << pred << " -> "
                          << amapit->first << messaget::eom;
            continue;
          }
          // OK, this is a flow from a similar but
          // distinct entry in the local var table.
          predecessor_map[&*it].insert(pred_var);
        }
      }
    }

    // If a simple pre-block initialiser was found,
    // add it to the live range now:
    it->var.length+=(it->var.start_pc-new_start_pc);
    it->var.start_pc=new_start_pc;
  }
}

/// Used to find out where to put a variable declaration that subsumes several
/// variable live ranges.
/// \par parameters: `merge_vars`: Set of variables we want the common dominator
///   for.
/// `dominator_analysis`: Already-initialised dominator tree
/// \return Returns the bytecode address of the closest common dominator of all
///   given variable table entries. In the worst case the function entry point
///   should always satisfy this criterion.
static unsigned get_common_dominator(
  const std::set<local_variable_with_holest*> &merge_vars,
  const java_cfg_dominatorst &dominator_analysis)
{
  PRECONDITION(!merge_vars.empty());

  unsigned first_pc=UINT_MAX;
  for(auto v : merge_vars)
  {
    if(v->var.start_pc<first_pc)
      first_pc=v->var.start_pc;
  }

  std::vector<unsigned> candidate_dominators;
  for(auto v : merge_vars)
  {
    const auto &dominator_nodeidx=
      dominator_analysis.cfg.entry_map.at(v->var.start_pc);
    const auto &this_var_doms=
      dominator_analysis.cfg[dominator_nodeidx].dominators;
    for(const auto this_var_dom : this_var_doms)
      if(this_var_dom<=first_pc)
        candidate_dominators.push_back(this_var_dom);
  }
  std::sort(candidate_dominators.begin(), candidate_dominators.end());

  // Working from the back, simply find the first PC
  // that occurs merge_vars.size() times and therefore
  // dominates all vars we seek to merge:
  for(auto domit=candidate_dominators.rbegin(),
        domitend=candidate_dominators.rend();
      domit!=domitend;
      /* Don't increment here */)
  {
    unsigned repeats=0;
    auto dom=*domit;
    while(domit!=domitend && *domit==dom)
    {
      ++domit;
      ++repeats;
    }
    assert(repeats<=merge_vars.size());
    if(repeats==merge_vars.size())
      return dom;
  }

  throw "variable live ranges with no common dominator?";
}

/// See above
/// \par parameters: `merge_vars`: a set of 2+ variable table entries to merge
/// `expanded_live_range_start`: address where the merged variable will be
///   declared
/// \return Adds holes to `merge_into`, indicating where gaps in the variable's
///   live range fall. For example, if the declaration happens at address 10 and
///   the entries in `merge_into` have live ranges [(20-30), (40-50)] then holes
///   will be added at (10-20) and (30-40).
static void populate_live_range_holes(
  local_variable_with_holest &merge_into,
  const std::set<local_variable_with_holest *> &merge_vars,
  unsigned expanded_live_range_start)
{
  std::vector<local_variable_with_holest *> sorted_by_startpc(
    merge_vars.begin(), merge_vars.end());
  std::sort(sorted_by_startpc.begin(), sorted_by_startpc.end(), lt_startpc);

  maybe_add_hole(
    merge_into,
    expanded_live_range_start,
    sorted_by_startpc[0]->var.start_pc);
  for(unsigned idx=0; idx<sorted_by_startpc.size()-1; ++idx)
  {
    maybe_add_hole(
      merge_into,
      sorted_by_startpc[idx]->var.start_pc+sorted_by_startpc[idx]->var.length,
      sorted_by_startpc[idx+1]->var.start_pc);
  }
}

/// See above
/// \par parameters: `merge_vars`: a set of 2+ variable table entries to merge
/// `dominator_analysis`: already-calculated dominator tree
/// \return Populates `merge_into` as a combined variable table entry, with live
///   range holes if the `merge_vars` entries do not cover a contiguous address
///   range, beginning the combined live range at the common dominator of all
///   `merge_vars`.
static void merge_variable_table_entries(
  local_variable_with_holest &merge_into,
  const std::set<local_variable_with_holest *> &merge_vars,
  const java_cfg_dominatorst &dominator_analysis,
  std::ostream &debug_out)
{
  // Because we need a lexically-scoped declaration,
  // we must have the merged variable
  // enter scope both in a block that dominates all entries, and which
  // precedes them in program order.
  unsigned found_dominator=
    get_common_dominator(merge_vars, dominator_analysis);

  // Populate the holes in the live range
  // (addresses where the new variable will be in scope,
  // but references to this stack slot should not resolve to it
  // as it was not visible in the original local variable table)
  populate_live_range_holes(merge_into, merge_vars, found_dominator);

  unsigned last_pc=0;
  for(auto v : merge_vars)
  {
    if(v->var.start_pc+v->var.length>last_pc)
      last_pc=v->var.start_pc+v->var.length;
  }

  // Apply the changes:
  merge_into.var.start_pc=found_dominator;
  merge_into.var.length=last_pc-found_dominator;

#ifdef DEBUG
  debug_out << "Merged " << merge_vars.size() << " variables named "
            << merge_into.var.name << "; new live range "
            << merge_into.var.start_pc << '-'
            << merge_into.var.start_pc + merge_into.var.length << '\n';
#endif

  // Nuke the now-subsumed var-table entries:
  for(auto &v : merge_vars)
    if(v!=&merge_into)
      v->var.length=0;
}

/// Given a sequence of users of the same local variable slot, this figures out
/// which ones are related by control flow, and combines them into a single
/// entry with holes, such that after combination we can create a single
/// declaration per variable table entry, placed at the live range's start
/// address, which may be moved back so that the declaration dominates all uses.
/// \par parameters: `firstvar`-`varlimit`: sequence of variable table entries,
///   all of which should concern the same slot index.
/// `amap`: Map from bytecode address to instruction
/// \return Side-effect: merges variable table entries which flow into one
///   another (e.g. there are branches from one live range to another without
///   re-initialising the local slot).
void java_bytecode_convert_methodt::find_initialisers_for_slot(
  local_variable_table_with_holest::iterator firstvar,
  local_variable_table_with_holest::iterator varlimit,
  const address_mapt &amap,
  const java_cfg_dominatorst &dominator_analysis)
{
  // Build a simple map from instruction PC to the variable
  // live in this slot at that PC, and a map from each variable
  // to variables that flow into it:
  std::vector<local_variable_with_holest *> live_variable_at_address;
  populate_variable_address_map(firstvar, varlimit, live_variable_at_address);

  // Now find variables that flow together by
  // walking backwards to find initialisers
  // or branches from other live ranges:
  predecessor_mapt predecessor_map;
  populate_predecessor_map(
    firstvar,
    varlimit,
    live_variable_at_address,
    amap,
    predecessor_map,
    get_message_handler());

  // OK, we've established the flows all seem sensible.
  // Now merge vartable entries according to the predecessor_map:

  // Take the transitive closure of the predecessor map:
  for(auto &kv : predecessor_map)
  {
    std::set<local_variable_with_holest *> closed_preds;
    gather_transitive_predecessors(kv.first, predecessor_map, closed_preds);
    kv.second=std::move(closed_preds);
  }

  // Top-sort so that we get the bottom variables first:
  is_predecessor_oft comp(predecessor_map);
  std::vector<local_variable_with_holest *> topsorted_vars;
  for(auto it=firstvar, itend=varlimit; it!=itend; ++it)
    topsorted_vars.push_back(&*it);

  std::sort(topsorted_vars.begin(), topsorted_vars.end(), comp);

  // Now merge the entries:
  for(auto merge_into : topsorted_vars)
  {
    // Already merged into another variable?
    if(merge_into->var.length==0)
      continue;

    auto findit=predecessor_map.find(merge_into);
    // Nothing to do?
    if(findit==predecessor_map.end())
      continue;

    const auto &merge_vars=findit->second;
    assert(merge_vars.size()>=2);

    merge_variable_table_entries(
      *merge_into,
      merge_vars,
      dominator_analysis,
      status());
  }
}

/// Walk a vector, a contiguous block of entries with equal slot index at a
/// time.
/// \par parameters: `it1` and `it2`, which are iterators into the same vector,
/// of which `itend` is the end() iterator.
/// \return Moves `it1` and `it2` to delimit a sequence of variable table
///   entries with slot index equal to it2->var.index on entering this function,
///   or to both equal itend if it2==itend on entry.
static void walk_to_next_index(
  local_variable_table_with_holest::iterator &it1,
  local_variable_table_with_holest::iterator &it2,
  local_variable_table_with_holest::iterator itend)
{
  if(it2==itend)
  {
    it1=itend;
    return;
  }

  auto old_it2=it2;
  auto index=it2->var.index;
  while(it2!=itend && it2->var.index==index)
    ++it2;
  it1=old_it2;
}

/// See `find_initialisers_for_slot` above for more detail.
/// \par parameters: `vars`: Local variable table
/// `amap`: Map from bytecode index to instruction
/// `dominator_analysis`: Already computed dominator tree for the Java function
///   described by `amap`
/// \return Combines entries in `vars` which flow together
void java_bytecode_convert_methodt::find_initialisers(
  local_variable_table_with_holest &vars,
  const address_mapt &amap,
  const java_cfg_dominatorst &dominator_analysis)
{
  // Sort table entries by local slot index:
  std::sort(vars.begin(), vars.end(), lt_index);

  // For each block of entries using a particular index,
  // try to combine them:
  auto it1=vars.begin();
  auto it2=it1;
  auto itend=vars.end();
  walk_to_next_index(it1, it2, itend);
  for(; it1!=itend; walk_to_next_index(it1, it2, itend))
    find_initialisers_for_slot(it1, it2, amap, dominator_analysis);
}

/// See above
/// \par parameters: `vars_with_holes`: variable table
/// \return Removes zero-size entries from `vars_with_holes`
static void cleanup_var_table(
  std::vector<local_variable_with_holest> &vars_with_holes)
{
  size_t toremove=0;
  for(size_t i=0; i<(vars_with_holes.size()-toremove); ++i)
  {
    auto &v=vars_with_holes[i];
    if(v.var.length==0)
    {
      // Move to end; consider the new element we've swapped in:
      ++toremove;
      if(i!=vars_with_holes.size()-toremove) // Already where it needs to be?
        std::swap(v, vars_with_holes[vars_with_holes.size()-toremove]);
      --i; // May make i (size_t)-1, but it will immediately be
           // re-incremented as the loop iterates.
    }
  }

  // Remove un-needed entries.
  vars_with_holes.resize(vars_with_holes.size()-toremove);
}

/// See `find_initialisers_for_slot` above for more detail.
/// \par parameters: `m`: Java method
/// `amap`: Map from bytecode indices to instructions in `m`
/// \return Populates `this->vars_with_holes` equal to
///   `this->local_variable_table`, only with variable table entries that flow
///   together combined. Also symbol-table registers all locals.
void java_bytecode_convert_methodt::setup_local_variables(
  const methodt &m,
  const address_mapt &amap)
{
  // Compute CFG dominator tree
  java_cfg_dominatorst dominator_analysis;
  method_with_amapt dominator_args(m, amap);
  dominator_analysis(dominator_args);

  // Find out which local variable table entries should be merged:
  // Wrap each entry so we have a data structure to work during function calls,
  // where we record live ranges with holes:
  std::vector<local_variable_with_holest> vars_with_holes;
  for(const auto &v : m.local_variable_table)
    vars_with_holes.push_back({v, is_parameter(v), {}});

  // Merge variable records:
  find_initialisers(vars_with_holes, amap, dominator_analysis);

  // Clean up removed records from the variable table:
  cleanup_var_table(vars_with_holes);

  // Do the locals and parameters in the variable table, which is available when
  // compiled with -g or for methods with many local variables in the latter
  // case, different variables can have the same index, depending on the
  // context.
  //
  // to calculate which variable to use, one uses the address of the instruction
  // that uses the variable, the size of the instruction and the start_pc /
  // length values in the local variable table
  for(const auto &v : vars_with_holes)
  {
    if(v.is_parameter)
      continue;

    typet t=java_type_from_string(v.var.signature);
    std::ostringstream id_oss;
    id_oss << method_id << "::" << v.var.start_pc << "::" << v.var.name;
    irep_idt identifier(id_oss.str());
    symbol_exprt result(identifier, t);
    result.set(ID_C_base_name, v.var.name);

    variables[v.var.index].push_back(variablet());
    auto &newv=variables[v.var.index].back();
    newv.symbol_expr=result;
    newv.start_pc=v.var.start_pc;
    newv.length=v.var.length;
    newv.holes=std::move(v.holes);

    symbolt new_symbol;
    new_symbol.name=identifier;
    new_symbol.type=t;
    new_symbol.base_name=v.var.name;
    new_symbol.pretty_name=id2string(identifier).substr(6, std::string::npos);
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;
    new_symbol.is_file_local=true;
    new_symbol.is_thread_local=true;
    new_symbol.is_lvalue=true;
    symbol_table.add(new_symbol);
  }
}

/// See above
/// \par parameters: `address`: Address to find a variable table entry for
/// `var_list`: List of candidates that use the slot we're interested in
/// \return Returns the list entry covering this address (taking live range
///   holes into account), or creates/returns an anonymous variable entry if
///   nothing covers `address`.
const java_bytecode_convert_methodt::variablet &
java_bytecode_convert_methodt::find_variable_for_slot(
  size_t address,
  variablest &var_list)
{
  for(const variablet &var : var_list)
  {
    size_t start_pc=var.start_pc;
    size_t length=var.length;
    if(address>=start_pc && address<(start_pc+length))
    {
      bool found_hole=false;
      for(auto &hole : var.holes)
        if(address>=hole.start_pc && address<(hole.start_pc+hole.length))
        {
          found_hole=true;
          break;
        }
      if(found_hole)
        continue;
      return var;
    }
  }
  // add unnamed local variable to end of list at this index
  // with scope from 0 to SIZE_T_MAX
  // as it is at the end of the vector, it will only be taken into account
  // if no other variable is valid
  size_t list_length=var_list.size();
  var_list.resize(list_length+1);
  var_list[list_length].start_pc=0;
  var_list[list_length].length=std::numeric_limits<size_t>::max();
  return var_list[list_length];
}
