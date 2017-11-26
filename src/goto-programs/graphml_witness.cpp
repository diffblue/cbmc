/*******************************************************************\

Module: Witnesses for Traces and Proofs

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Witnesses for Traces and Proofs

#include <iostream>

#include "graphml_witness.h"

#include <util/base_type.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/arith_tools.h>
#include <util/prefix.h>
#include <util/ssa_expr.h>
#include <util/std_pair_hash.h>
#include <unordered_map>

#include <langapi/language_util.h>
#include <langapi/mode.h>

#include <ansi-c/expr2c.h>

#include "goto_program.h"

static std::string expr_to_string(
  const namespacet &ns,
  const irep_idt &id,
  const exprt &expr)
{
  if(get_mode_from_identifier(ns, id) == ID_C)
    return expr2c(expr, ns, expr2c_configurationt::clean_configuration);
  else
    return from_expr(ns, id, expr);
}

void graphml_witnesst::remove_l0_l1(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    if(is_ssa_expr(expr))
      expr=to_ssa_expr(expr).get_original_expr();
    else
    {
      std::string identifier=
        id2string(to_symbol_expr(expr).get_identifier());

      std::string::size_type l0_l1=identifier.find_first_of("!@");
      if(l0_l1!=std::string::npos)
      {
        identifier.resize(l0_l1);
        to_symbol_expr(expr).set_identifier(identifier);
      }
    }

    return;
  }

  Forall_operands(it, expr)
    remove_l0_l1(*it);
}

std::string graphml_witnesst::convert_assign_rec(
  const irep_idt &identifier,
  const code_assignt &assign)
{
  static std::unordered_map<std::pair<unsigned int, const irept::dt *>, std::string> cache;
  {
      const auto cit = cache.find({identifier.get_no(), &assign.read()});
      if(cit != cache.end())
          return cit->second;
  }

  std::string result;

  if(assign.rhs().id()=="array-list")
  {
    const array_typet &type=
      to_array_type(ns.follow(assign.rhs().type()));

    const auto ops=assign.rhs().operands();
    DATA_INVARIANT(
      ops.size()%2==0,
      "array-list has odd number of operands");

    for(size_t listidx=0; listidx!=ops.size(); listidx+=2)
    {
      index_exprt index(
        assign.lhs(),
        ops[listidx],
        type.subtype());
      if(!result.empty())
        result+=' ';
      result+=
        convert_assign_rec(identifier, code_assignt(index, ops[listidx+1]));
    }
  }
  else if(assign.rhs().id()==ID_array)
  {
    const array_typet &type=
      to_array_type(ns.follow(assign.rhs().type()));

    unsigned i=0;
    forall_operands(it, assign.rhs())
    {
      index_exprt index(
        assign.lhs(),
        from_integer(i++, index_type()),
        type.subtype());
      if(!result.empty())
        result+=' ';
      result+=convert_assign_rec(identifier, code_assignt(index, *it));
    }
  }
  else if(assign.rhs().id()==ID_struct ||
          assign.rhs().id()==ID_union)
  {
    // dereferencing may have resulted in an lhs that is the first
    // struct member; undo this
    if(assign.lhs().id()==ID_member &&
       !base_type_eq(assign.lhs().type(), assign.rhs().type(), ns))
    {
      code_assignt tmp=assign;
      tmp.lhs()=to_member_expr(assign.lhs()).struct_op();

      return convert_assign_rec(identifier, tmp);
    }
    else if(assign.lhs().id()==ID_byte_extract_little_endian ||
            assign.lhs().id()==ID_byte_extract_big_endian)
    {
      code_assignt tmp=assign;
      tmp.lhs()=to_byte_extract_expr(assign.lhs()).op();

      return convert_assign_rec(identifier, tmp);
    }

    const struct_union_typet &type=
      to_struct_union_type(ns.follow(assign.lhs().type()));
    const struct_union_typet::componentst &components=
      type.components();

    exprt::operandst::const_iterator it=
      assign.rhs().operands().begin();
    for(const auto &comp : components)
    {
      if(comp.type().id()==ID_code ||
         comp.get_is_padding() ||
         // for some reason #is_padding gets lost in *some* cases
         has_prefix(id2string(comp.get_name()), "$pad"))
        continue;

      INVARIANT(
        it != assign.rhs().operands().end(), "expression must have operands");

      member_exprt member(
        assign.lhs(),
        comp.get_name(),
        it->type());
      if(!result.empty())
        result+=' ';
      result+=convert_assign_rec(identifier, code_assignt(member, *it));
      ++it;

      // for unions just assign to the first member
      if(assign.rhs().id()==ID_union)
        break;
    }
  }
  else
  {
    exprt clean_rhs=assign.rhs();
    remove_l0_l1(clean_rhs);

    exprt clean_lhs=assign.lhs();
    remove_l0_l1(clean_lhs);
    std::string lhs=expr_to_string(ns, identifier, clean_lhs);
    if(lhs.find('$')!=std::string::npos)
      lhs="\\result";

    result=lhs+" = "+expr_to_string(ns, identifier, clean_rhs)+";";
  }
  cache.insert({{identifier.get_no(), &assign.read()}, result});
  return result;
}

static bool filter_out(
  const goto_tracet &goto_trace,
  const goto_tracet::stepst::const_iterator &prev_it,
  goto_tracet::stepst::const_iterator &it)
{
  if(it->hidden &&
     (!it->pc->is_assign() ||
      to_code_assign(it->pc->code).rhs().id()!=ID_side_effect ||
      to_code_assign(it->pc->code).rhs().get(ID_statement)!=ID_nondet))
    return true;

  if(!it->is_assignment() && !it->is_goto() && !it->is_assert())
    return true;

  // we filter out steps with the same source location
  // TODO: if these are assignments we should accumulate them into
  //       a single edge
  if(prev_it!=goto_trace.steps.end() &&
     prev_it->pc->source_location==it->pc->source_location)
    return true;

  if(it->is_goto() && it->pc->guard.is_true())
    return true;

  const source_locationt &source_location=it->pc->source_location;

  if(source_location.is_nil() ||
     source_location.get_file().empty() ||
     source_location.is_built_in() ||
     source_location.get_line().empty())
    return true;

  return false;
}

static bool contains_symbol_prefix(const exprt &expr, const std::string &prefix){
  if(expr.id()==ID_symbol &&
     has_prefix(id2string(to_symbol_expr(expr).get_identifier()), prefix))
  {
    return true;
  }

  forall_operands(it, expr)
  {
    if(contains_symbol_prefix(*it, prefix))
      return true;
  }
  return false;
}

/// counterexample witness
void graphml_witnesst::operator()(const goto_tracet &goto_trace)
{
  graphml.key_values["sourcecodelang"]="C";

  const graphmlt::node_indext sink=graphml.add_node();
  graphml[sink].node_name="sink";
  graphml[sink].is_violation=false;
  graphml[sink].has_invariant=false;

  // step numbers start at 1
  std::vector<std::size_t> step_to_node(goto_trace.steps.size()+1, 0);

  goto_tracet::stepst::const_iterator prev_it=goto_trace.steps.end();
  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++) // we cannot replace this by a ranged for
  {
    if(filter_out(goto_trace, prev_it, it))
    {
      step_to_node[it->step_nr]=sink;

      continue;
    }

    // skip declarations followed by an immediate assignment
    goto_tracet::stepst::const_iterator next=it;
    ++next;
    if(next!=goto_trace.steps.end() &&
       next->type==goto_trace_stept::typet::ASSIGNMENT &&
       it->full_lhs==next->full_lhs &&
       it->pc->source_location==next->pc->source_location)
    {
      step_to_node[it->step_nr]=sink;

      continue;
    }

    prev_it=it;

    const source_locationt &source_location=it->pc->source_location;

    const graphmlt::node_indext node=graphml.add_node();
    graphml[node].node_name=
      std::to_string(it->pc->location_number)+"."+std::to_string(it->step_nr);
    graphml[node].file=source_location.get_file();
    graphml[node].line=source_location.get_line();
    graphml[node].is_violation=
      it->type==goto_trace_stept::typet::ASSERT && !it->cond_value;
    graphml[node].has_invariant=false;

    step_to_node[it->step_nr]=node;
  }

  std::size_t thread_id=0;

  // build edges
  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      ) // no ++it
  {
    const std::size_t from=step_to_node[it->step_nr];

    // no outgoing edges from sinks or violation nodes
    if(from==sink || graphml[from].is_violation)
    {
      ++it;
      continue;
    }

    auto next = std::next(it);
    for(; next != goto_trace.steps.end() &&
          (step_to_node[next->step_nr] == sink ||
           pointee_address_equalt{}(it->pc, next->pc)); // NOLINT
        ++next)
    {
      // advance
    }
    const std::size_t to=
      next==goto_trace.steps.end()?
      sink:step_to_node[next->step_nr];

    switch(it->type)
    {
    case goto_trace_stept::typet::ASSIGNMENT:
    case goto_trace_stept::typet::ASSERT:
    case goto_trace_stept::typet::GOTO:
    case goto_trace_stept::typet::SPAWN:
      {
        xmlt edge("edge");
        edge.set_attribute("source", graphml[from].node_name);
        edge.set_attribute("target", graphml[to].node_name);

        {
          xmlt &data_f=edge.new_element("data");
          data_f.set_attribute("key", "originfile");
          data_f.data=id2string(graphml[from].file);

          xmlt &data_l=edge.new_element("data");
          data_l.set_attribute("key", "startline");
          data_l.data=id2string(graphml[from].line);

          xmlt &data_t=edge.new_element("data");
          data_t.set_attribute("key", "threadId");
          data_t.data=std::to_string(it->thread_nr);
        }

        if(it->type==goto_trace_stept::typet::ASSIGNMENT &&
           it->full_lhs_value.is_not_nil() &&
           it->full_lhs.is_not_nil() &&
           it->full_lhs.id() == ID_symbol)
        {
          const symbol_exprt &lhs_symbol = to_symbol_expr(it->full_lhs);
          if(id2string(lhs_symbol.get_identifier())
             .find("pthread_create::thread")!=std::string::npos)
          {
            xmlt &data_t=edge.new_element("data");
            data_t.set_attribute("key", "createThread");
            data_t.data=std::to_string(++thread_id);
          }
          else if(
            id2string(lhs_symbol.get_identifier())
              .find("#return_value")==std::string::npos &&
            !contains_symbol_prefix(
              it->full_lhs_value, "symex_dynamic::dynamic_object") &&
            !contains_symbol_prefix(
              it->full_lhs, "symex_dynamic::dynamic_object") &&
            id2string(lhs_symbol.get_identifier())
              .find("thread")==std::string::npos &&
            id2string(lhs_symbol.get_identifier())
              .find("mutex")==std::string::npos &&
            (!it->full_lhs_value.is_constant() ||
             !it->full_lhs_value.has_operands() ||
             !has_prefix(id2string(it->full_lhs_value.op0().get(ID_value)),
                         "INVALID-")))
          {
            xmlt &val=edge.new_element("data");
            val.set_attribute("key", "assumption");
            code_assignt assign(it->full_lhs, it->full_lhs_value);
            irep_idt identifier=lhs_symbol.get_identifier();
            val.data=convert_assign_rec(identifier, assign);

            xmlt &val_s=edge.new_element("data");
            val_s.set_attribute("key", "assumption.scope");
            val_s.data=id2string(it->pc->source_location.get_function());
          }
        }
        else if(it->type==goto_trace_stept::typet::GOTO &&
                it->pc->is_goto())
        {
        }

        graphml[to].in[from].xml_node=edge;
        graphml[from].out[to].xml_node=edge;
      }
      break;

    case goto_trace_stept::typet::DECL:
    case goto_trace_stept::typet::FUNCTION_CALL:
    case goto_trace_stept::typet::FUNCTION_RETURN:
    case goto_trace_stept::typet::LOCATION:
    case goto_trace_stept::typet::ASSUME:
    case goto_trace_stept::typet::INPUT:
    case goto_trace_stept::typet::OUTPUT:
    case goto_trace_stept::typet::SHARED_READ:
    case goto_trace_stept::typet::SHARED_WRITE:
    case goto_trace_stept::typet::MEMORY_BARRIER:
    case goto_trace_stept::typet::ATOMIC_BEGIN:
    case goto_trace_stept::typet::ATOMIC_END:
    case goto_trace_stept::typet::DEAD:
    case goto_trace_stept::typet::CONSTRAINT:
    case goto_trace_stept::typet::NONE:
      // ignore
      break;
    }

    it=next;
  }
}

/// proof witness
void graphml_witnesst::operator()(const symex_target_equationt &equation)
{
  graphml.key_values["sourcecodelang"]="C";

  const graphmlt::node_indext sink=graphml.add_node();
  graphml[sink].node_name="sink";
  graphml[sink].is_violation=false;
  graphml[sink].has_invariant=false;

  // step numbers start at 1
  std::vector<std::size_t> step_to_node(equation.SSA_steps.size()+1, 0);

  std::size_t step_nr=1;
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++, step_nr++) // we cannot replace this by a ranged for
  {
    const source_locationt &source_location=it->source.pc->source_location;

    if(it->hidden ||
       (!it->is_assignment() && !it->is_goto() && !it->is_assert()) ||
       (it->is_goto() && it->source.pc->guard.is_true()) ||
       source_location.is_nil() ||
       source_location.is_built_in() ||
       source_location.get_line().empty())
    {
      step_to_node[step_nr]=sink;

      continue;
    }

    // skip declarations followed by an immediate assignment
    symex_target_equationt::SSA_stepst::const_iterator next=it;
    ++next;
    if(next!=equation.SSA_steps.end() &&
       next->is_assignment() &&
       it->ssa_full_lhs==next->ssa_full_lhs &&
       it->source.pc->source_location==next->source.pc->source_location)
    {
      step_to_node[step_nr]=sink;

      continue;
    }

    const graphmlt::node_indext node=graphml.add_node();
    graphml[node].node_name=
      std::to_string(it->source.pc->location_number)+"."+
      std::to_string(step_nr);
    graphml[node].file=source_location.get_file();
    graphml[node].line=source_location.get_line();
    graphml[node].is_violation=false;
    graphml[node].has_invariant=false;

    step_to_node[step_nr]=node;
  }

  // build edges
  step_nr=1;
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      ) // no ++it
  {
    const std::size_t from=step_to_node[step_nr];

    if(from==sink)
    {
      ++it;
      ++step_nr;
      continue;
    }

    symex_target_equationt::SSA_stepst::const_iterator next=it;
    std::size_t next_step_nr=step_nr;
    for(++next, ++next_step_nr;
        next!=equation.SSA_steps.end() &&
        (step_to_node[next_step_nr]==sink || it->source.pc==next->source.pc);
        ++next, ++next_step_nr)
    {
      // advance
    }
    const std::size_t to=
      next==equation.SSA_steps.end()?
      sink:step_to_node[next_step_nr];

    switch(it->type)
    {
    case goto_trace_stept::typet::ASSIGNMENT:
    case goto_trace_stept::typet::ASSERT:
    case goto_trace_stept::typet::GOTO:
    case goto_trace_stept::typet::SPAWN:
      {
        xmlt edge("edge");
        edge.set_attribute("source", graphml[from].node_name);
        edge.set_attribute("target", graphml[to].node_name);

        {
          xmlt &data_f=edge.new_element("data");
          data_f.set_attribute("key", "originfile");
          data_f.data=id2string(graphml[from].file);

          xmlt &data_l=edge.new_element("data");
          data_l.set_attribute("key", "startline");
          data_l.data=id2string(graphml[from].line);
        }

        if((it->is_assignment() ||
            it->is_decl()) &&
           it->ssa_rhs.is_not_nil() &&
           it->ssa_full_lhs.is_not_nil())
        {
          irep_idt identifier=it->ssa_lhs.get_object_name();

          graphml[to].has_invariant=true;
          code_assignt assign(it->ssa_full_lhs, it->ssa_rhs);
          graphml[to].invariant=convert_assign_rec(identifier, assign);
          graphml[to].invariant_scope=
            id2string(it->source.pc->source_location.get_function());
        }

        graphml[to].in[from].xml_node=edge;
        graphml[from].out[to].xml_node=edge;
      }
      break;

    case goto_trace_stept::typet::DECL:
    case goto_trace_stept::typet::FUNCTION_CALL:
    case goto_trace_stept::typet::FUNCTION_RETURN:
    case goto_trace_stept::typet::LOCATION:
    case goto_trace_stept::typet::ASSUME:
    case goto_trace_stept::typet::INPUT:
    case goto_trace_stept::typet::OUTPUT:
    case goto_trace_stept::typet::SHARED_READ:
    case goto_trace_stept::typet::SHARED_WRITE:
    case goto_trace_stept::typet::MEMORY_BARRIER:
    case goto_trace_stept::typet::ATOMIC_BEGIN:
    case goto_trace_stept::typet::ATOMIC_END:
    case goto_trace_stept::typet::DEAD:
    case goto_trace_stept::typet::CONSTRAINT:
    case goto_trace_stept::typet::NONE:
      // ignore
      break;
    }

    it=next;
    step_nr=next_step_nr;
  }
}
