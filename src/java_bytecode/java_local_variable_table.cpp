
#include "java_bytecode_convert_method_class.h"

#include <util/string2int.h>
#include "java_types.h"

#include <climits>

// Specialise the CFG representation to work over Java instead of GOTO programs.
// This must be done at global scope due to template resolution rules.

template<class T>
struct procedure_local_cfg_baset<T,const java_bytecode_convert_methodt::address_mapt,unsigned> :
    public graph<cfg_base_nodet<T, unsigned> >
{
  typedef java_bytecode_convert_methodt::address_mapt address_mapt;
  typedef std::map<unsigned, unsigned> entry_mapt;
  entry_mapt entry_map;

  procedure_local_cfg_baset() {}

  void operator()(const address_mapt& amap)
  {
    for(const auto& inst : amap)
    {
      // Map instruction PCs onto node indices:
      entry_map[inst.first]=this->add_node();
      // Map back:
      (*this)[entry_map[inst.first]].PC=inst.first;
    }
    for(const auto& inst : amap)
    {
      for(auto succ : inst.second.successors)
        this->add_edge(entry_map.at(inst.first),entry_map.at(succ));
    }
  }

  unsigned get_first_node(const address_mapt& amap) const { return amap.begin()->first; }
  unsigned get_last_node(const address_mapt& amap) const { return (--amap.end())->first; }
  unsigned nodes_empty(const address_mapt& amap) const { return amap.empty(); }

};

namespace {

typedef java_bytecode_convert_methodt::holet holet;
typedef java_bytecode_convert_methodt::local_variable_with_holest local_variable_with_holest;
typedef java_bytecode_convert_methodt::local_variable_table_with_holest local_variable_table_with_holest;
typedef java_bytecode_convert_methodt::address_mapt address_mapt;
typedef java_bytecode_convert_methodt::java_cfg_dominatorst java_cfg_dominatorst;

// Comparators for local variables:

static bool lt_index(const local_variable_with_holest& a,
              const local_variable_with_holest& b)
{
  return a.var.index<b.var.index;
}
static bool lt_startpc(const local_variable_with_holest* a,
                const local_variable_with_holest* b)
{
  return a->var.start_pc<b->var.start_pc;
}

// The predecessor map, and a top-sorting comparator:

typedef std::map<local_variable_with_holest*,
                 std::set<local_variable_with_holest*> > predecessor_mapt;

struct is_predecessor_of
{
  const predecessor_mapt& order;

  is_predecessor_of(const predecessor_mapt& _order) : order(_order) {}

  bool operator()(local_variable_with_holest* a,
                  local_variable_with_holest* b) const
  {
    auto findit=order.find(a);
    if(findit==order.end())
      return false;
    return findit->second.count(b)>0;
  }
};

// Helper routines for the find-initialisers code below:

static void gather_transitive_predecessors(
  local_variable_with_holest* start,
  const predecessor_mapt& predecessor_map,
  std::set<local_variable_with_holest*>& result)
{
  if(!result.insert(start).second)
    return;
  auto findit=predecessor_map.find(start);
  if(findit==predecessor_map.end())
    return;
  for(const auto pred : findit->second)
    gather_transitive_predecessors(pred,predecessor_map,result);
}

static bool is_store_to_slot(
  const java_bytecode_convert_methodt::instructiont& inst,
  unsigned slotidx)
{
  const std::string prevstatement=id2string(inst.statement);
  if(!(prevstatement.size()>=1 && prevstatement.substr(1,5)=="store"))
    return false;

  std::string storeslot;
  if(inst.args.size()==1)
  {
    const auto& arg=inst.args[0];
    storeslot=id2string(to_constant_expr(arg).get_value());
  }
  else
  {
    assert(prevstatement[6]=='_' && prevstatement.size()==8);
    storeslot=prevstatement[7];
    assert(isdigit(storeslot[0]));
  }
  auto storeslotidx=safe_string2unsigned(storeslot);
  return storeslotidx==slotidx;
}

static void maybe_add_hole(
  local_variable_with_holest& var,
  unsigned from,
  unsigned to)
{
  assert(to>=from);
  if(to!=from)
    var.holes.push_back({from,to-from});
}

static void populate_variable_address_map(
  local_variable_table_with_holest::iterator firstvar,
  local_variable_table_with_holest::iterator varlimit,
  std::vector<local_variable_with_holest*>& live_variable_at_address)
{
  for(auto it=firstvar, itend=varlimit; it!=itend; ++it)
  {
    if(it->var.start_pc+it->var.length > live_variable_at_address.size())
      live_variable_at_address.resize(it->var.start_pc+it->var.length);

    for(unsigned idx=it->var.start_pc,
          idxlim=it->var.start_pc+it->var.length;
        idx!=idxlim; ++idx)
    {
      assert((!live_variable_at_address[idx]) && "Local variable table clash?");
      live_variable_at_address[idx]=&*it;
    }
  }

}

static void populate_predecessor_map(
  local_variable_table_with_holest::iterator firstvar,
  local_variable_table_with_holest::iterator varlimit,
  const std::vector<local_variable_with_holest*>& live_variable_at_address,
  const address_mapt& amap,
  predecessor_mapt& predecessor_map)
{

  for(auto it=firstvar, itend=varlimit; it!=itend; ++it)
  {
    // Parameters are irrelevant to us and shouldn't be changed:
    if(it->var.start_pc==0)
      continue;

    // Find the last instruction within the live range:
    unsigned end_pc=it->var.start_pc+it->var.length;
    auto amapit=amap.find(end_pc);
    auto old_amapit=amapit;
    --amapit;
    if(old_amapit==amap.end())
      assert(end_pc>amapit->first &&
             "Instruction live range doesn't align to instruction boundary?");

    // Find vartable entries that flow into this one:
    unsigned new_start_pc=it->var.start_pc;
    for(; amapit->first >= it->var.start_pc; --amapit)
    {
      for(auto pred : amapit->second.predecessors)
      {
        auto pred_var=live_variable_at_address[pred];
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
          --inst_before_this;
          if(amapit->first!=it->var.start_pc || inst_before_this->first!=pred)
            throw "Local variable table: unexpected flow from out of range";
          if(!is_store_to_slot(*(inst_before_this->second.source),it->var.index))
            throw "Local variable table: didn't find expected initialising store";
          new_start_pc=pred;
        }
        else {
          if(pred_var->var.name!=it->var.name || pred_var->var.signature!=it->var.signature)
            throw "Local variable table: flow from variable with clashing name or signature";
          // OK, this is a flow from a similar but distinct entry in the local var table.
          predecessor_map[&*it].insert(pred_var);
        }
      }
    }

    // If a simple pre-block initialiser was found, add it to the live range now:
    it->var.length+=(it->var.start_pc-new_start_pc);
    it->var.start_pc=new_start_pc;

  }

}

static unsigned get_common_dominator(
  const std::set<local_variable_with_holest*>& merge_vars,
  const java_cfg_dominatorst& dominator_analysis)
{
  assert(merge_vars.size()!=0);

  unsigned first_pc=UINT_MAX;
  for(auto v : merge_vars)
  {
    if(v->var.start_pc < first_pc)
      first_pc = v->var.start_pc;
  }

  std::vector<unsigned> candidate_dominators;
  for(auto v : merge_vars)
  {
    const auto& dominator_nodeidx=dominator_analysis.cfg.entry_map.at(v->var.start_pc);
    const auto& this_var_doms=dominator_analysis.cfg[dominator_nodeidx].dominators;
    for(const auto this_var_dom : this_var_doms)
      if(this_var_dom <= first_pc)
        candidate_dominators.push_back(this_var_dom);
  }
  std::sort(candidate_dominators.begin(),candidate_dominators.end());

  // Working from the back, simply find the first PC that occurs merge_vars.size()
  // times and therefore dominates all vars we seek to merge:
  for(auto domit=candidate_dominators.rbegin(), domitend=candidate_dominators.rend();
      domit != domitend; /* Don't increment here */)
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

  throw "Variable live ranges with no common dominator?";
}

static void populate_live_range_holes(
  local_variable_with_holest& merge_into,
  const std::set<local_variable_with_holest*>& merge_vars,
  unsigned expanded_live_range_start)
{
  std::vector<local_variable_with_holest*> sorted_by_startpc(
    merge_vars.begin(),merge_vars.end());
  std::sort(sorted_by_startpc.begin(),sorted_by_startpc.end(),lt_startpc);

  maybe_add_hole(merge_into,expanded_live_range_start,sorted_by_startpc[0]->var.start_pc);
  for(unsigned idx=0; idx<sorted_by_startpc.size()-1; ++idx)
    maybe_add_hole(merge_into,
                   sorted_by_startpc[idx]->var.start_pc + sorted_by_startpc[idx]->var.length,
                   sorted_by_startpc[idx+1]->var.start_pc);
}

static void merge_variable_table_entries(
  local_variable_with_holest& merge_into,
  const std::set<local_variable_with_holest*>& merge_vars,
  const java_cfg_dominatorst& dominator_analysis,
  std::ostream& debug_out)
{
  // Because we need a lexically-scoped declaration, we must have the merged variable
  // enter scope both in a block that dominates all entries, and which
  // precedes them in program order.
  unsigned found_dominator=
    get_common_dominator(merge_vars,dominator_analysis);

  // Populate the holes in the live range (addresses where the new variable
  // will be in scope, but references to this stack slot should not resolve to it
  // as it was not visible in the original local variable table)
  populate_live_range_holes(merge_into,merge_vars,found_dominator);

  unsigned last_pc=0;
  for(auto v : merge_vars)
    if(v->var.start_pc+v->var.length > last_pc)
      last_pc=v->var.start_pc+v->var.length;

  // Apply the changes:
  merge_into.var.start_pc=found_dominator;
  merge_into.var.length=last_pc-found_dominator;

#ifdef DEBUG
  debug_out << "Merged " << merge_vars.size() << " variables named " << merge_into.var.name <<
    "; new live range " << merge_into.var.start_pc << "-" <<
    merge_into.var.start_pc + merge_into.var.length << messaget::eom;
#endif

  // Nuke the now-subsumed var-table entries:
  for(auto& v : merge_vars)
    if(v!=&merge_into)
      v->var.length=0;
}

} // End anonymous namespace

void java_bytecode_convert_methodt::find_initialisers_for_slot(
  local_variable_table_with_holest::iterator firstvar,
  local_variable_table_with_holest::iterator varlimit,
  const address_mapt& amap,
  const java_cfg_dominatorst& dominator_analysis)
{
  // Build a simple map from instruction PC to the variable live in this slot at that PC,
  // and a map from each variable to variables that flow into it:
  std::vector<local_variable_with_holest*> live_variable_at_address;
  populate_variable_address_map(firstvar,varlimit,live_variable_at_address);

  // Now find variables that flow together by walking backwards to find initialisers
  // or branches from other live ranges:
  predecessor_mapt predecessor_map;
  populate_predecessor_map(firstvar,varlimit,live_variable_at_address,amap,predecessor_map);

  // OK, we've established the flows all seem sensible. Now merge vartable entries
  // according to the predecessor_map:

  // Top-sort so that we get the bottom variables first:
  is_predecessor_of comp(predecessor_map);
  std::vector<local_variable_with_holest*> topsorted_vars;
  for(auto it=firstvar,itend=varlimit; it!=itend; ++it)
    topsorted_vars.push_back(&*it);

  std::sort(topsorted_vars.begin(),topsorted_vars.end(),comp);

  // Now merge the entries:
  for(auto merge_into : topsorted_vars)
  {
    // Already merged into another variable?
    if(merge_into->var.length==0)
      continue;

    std::set<local_variable_with_holest*> merge_vars;
    gather_transitive_predecessors(merge_into,predecessor_map,merge_vars);
    // Nothing to do?
    if(merge_vars.size()==1)
      continue;

    merge_variable_table_entries(*merge_into,merge_vars,dominator_analysis,status());
  }

}

static void walk_to_next_index(
  local_variable_table_with_holest::iterator& it1,
  local_variable_table_with_holest::iterator& it2,
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

void java_bytecode_convert_methodt::find_initialisers(
  local_variable_table_with_holest& vars,
  const address_mapt& amap,
  const java_cfg_dominatorst& dominator_analysis)
{
  // Handle one stack slot at a time:
  std::sort(vars.begin(),vars.end(),lt_index);

  auto it1=vars.begin();
  auto it2=it1;
  auto itend=vars.end();
  walk_to_next_index(it1,it2,itend);
  for(; it1!=itend; walk_to_next_index(it1,it2,itend))
    find_initialisers_for_slot(it1,it2,amap,dominator_analysis);
}

static void cleanup_var_table(std::vector<local_variable_with_holest>& vars_with_holes)
{
  size_t toremove=0;
  for(size_t i=0; i<(vars_with_holes.size()-toremove); ++i)
  {
    auto& v=vars_with_holes[i];
    if(v.var.length==0)
    {
      // Move to end; consider the new element we've swapped in:
      ++toremove;
      if(i!=vars_with_holes.size()-toremove) // Already where it needs to be?
        std::swap(v,vars_with_holes[vars_with_holes.size()-toremove]);
      --i;
    }
  }

  // Remove un-needed entries.
  vars_with_holes.resize(vars_with_holes.size()-toremove);
}

void java_bytecode_convert_methodt::setup_local_variables(const methodt& m,
                                                          const address_mapt& amap)
{
  // Compute CFG dominator tree
  java_cfg_dominatorst dominator_analysis;
  dominator_analysis(amap);

  // Find out which local variable table entries should be merged:
  // Wrap each entry so we have somewhere to record live ranges with holes:
  std::vector<local_variable_with_holest> vars_with_holes;
  for(const auto& v : m.local_variable_table)
    vars_with_holes.push_back({v, {}});

  // Merge variable records:
  find_initialisers(vars_with_holes,amap,dominator_analysis);

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
  for(const auto & v : vars_with_holes)
  {
    if(v.var.start_pc==0) // Parameter?
      continue;

    typet t=java_type_from_string(v.var.signature);
    std::ostringstream id_oss;
    id_oss << method_id << "::" << v.var.start_pc << "::" << v.var.name;
    irep_idt identifier(id_oss.str());
    symbol_exprt result(identifier, t);
    result.set(ID_C_base_name, v.var.name);

    variables[v.var.index].push_back(variablet());
    auto& newv=variables[v.var.index].back();
    newv.symbol_expr = result;
    newv.start_pc = v.var.start_pc;
    newv.length = v.var.length;
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

const java_bytecode_convert_methodt::variablet &
java_bytecode_convert_methodt::find_variable_for_slot(
  size_t address,
  variablest &var_list)
{
  for(const variablet &var : var_list)
  {
    size_t start_pc = var.start_pc;
    size_t length = var.length;
    if (address>=start_pc && address<(start_pc+length))
    {
      bool found_hole=false;
      for(auto &hole : var.holes)
        if(address>=hole.start_pc && address<(hole.start_pc-hole.length))
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
  // with scope from 0 to INT_MAX
  // as it is at the end of the vector, it will only be taken into account
  // if no other variable is valid
  size_t list_length = var_list.size();
  var_list.resize(list_length+1);
  var_list[list_length].start_pc=0;
  var_list[list_length].length=std::numeric_limits<size_t>::max();
  return var_list[list_length];
}
