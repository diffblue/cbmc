/*******************************************************************\

Module: Witnesses for Traces and Proofs

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Witnesses for Traces and Proofs

#include "graphml_witness.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/ssa_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table.h>

#include <langapi/language_util.h>
#include <langapi/mode.h>

#include <goto-symex/symex_target_equation.h>

#include <ansi-c/expr2c.h>

#include "goto_program.h"
#include "goto_trace.h"

static std::string
expr_to_string(const namespacet &ns, const irep_idt &id, const exprt &expr)
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
  else if(expr.id() == ID_string_constant)
  {
    std::string output_string = expr_to_string(ns, "", expr);
    if(!xmlt::is_printable_xml(output_string))
      expr = to_string_constant(expr).to_array_expr();
  }

  Forall_operands(it, expr)
    remove_l0_l1(*it);
}

std::string graphml_witnesst::convert_assign_rec(
  const irep_idt &identifier,
  const code_assignt &assign)
{
#ifdef USE_DSTRING
  const auto cit = cache.find({identifier.get_no(), &assign.read()});
#else
  const auto cit =
    cache.find({get_string_container()[id2string(identifier)], &assign.read()});
#endif
  if(cit != cache.end())
    return cit->second;

  std::string result;

  if(assign.rhs().id() == ID_array_list)
  {
    const array_list_exprt &array_list = to_array_list_expr(assign.rhs());
    const auto &ops = array_list.operands();

    for(std::size_t listidx = 0; listidx != ops.size(); listidx += 2)
    {
      const index_exprt index{assign.lhs(), ops[listidx]};
      if(!result.empty())
        result += ' ';
      result +=
        convert_assign_rec(identifier, code_assignt{index, ops[listidx + 1]});
    }
  }
  else if(assign.rhs().id() == ID_array)
  {
    const array_typet &type = to_array_type(assign.rhs().type());

    unsigned i=0;
    forall_operands(it, assign.rhs())
    {
      index_exprt index(
        assign.lhs(), from_integer(i++, c_index_type()), type.element_type());
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
    if(
      assign.lhs().id() == ID_member &&
      assign.lhs().type() != assign.rhs().type())
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
  else if(assign.rhs().id() == ID_with)
  {
    const with_exprt &with_expr = to_with_expr(assign.rhs());
    const auto &ops = with_expr.operands();

    for(std::size_t i = 1; i < ops.size(); i += 2)
    {
      if(!result.empty())
        result += ' ';

      if(ops[i].id() == ID_member_name)
      {
        const member_exprt member{
          assign.lhs(), ops[i].get(ID_component_name), ops[i + 1].type()};
        result +=
          convert_assign_rec(identifier, code_assignt(member, ops[i + 1]));
      }
      else
      {
        const index_exprt index{assign.lhs(), ops[i]};
        result +=
          convert_assign_rec(identifier, code_assignt(index, ops[i + 1]));
      }
    }
  }
  else
  {
    exprt clean_rhs=assign.rhs();
    remove_l0_l1(clean_rhs);

    exprt clean_lhs = assign.lhs();
    remove_l0_l1(clean_lhs);
    std::string lhs = expr_to_string(ns, identifier, clean_lhs);

    if(
      lhs.find("#return_value") != std::string::npos ||
      (lhs.find('$') != std::string::npos &&
       has_prefix(lhs, "return_value___VERIFIER_nondet_")))
    {
      lhs="\\result";
    }

    result = lhs + " = " + expr_to_string(ns, identifier, clean_rhs) + ";";
  }

#ifdef USE_DSTRING
  cache.insert({{identifier.get_no(), &assign.read()}, result});
#else
  cache.insert(
    {{get_string_container()[id2string(identifier)], &assign.read()}, result});
#endif
  return result;
}

static bool filter_out(
  const goto_tracet &goto_trace,
  const goto_tracet::stepst::const_iterator &prev_it,
  goto_tracet::stepst::const_iterator &it)
{
  if(
    it->hidden &&
    (!it->pc->is_assign() || it->pc->assign_rhs().id() != ID_side_effect ||
     it->pc->assign_rhs().get(ID_statement) != ID_nondet))
    return true;

  if(!it->is_assignment() && !it->is_goto() && !it->is_assert())
    return true;

  // we filter out steps with the same source location
  // TODO: if these are assignments we should accumulate them into
  //       a single edge
  if(
    prev_it != goto_trace.steps.end() &&
    prev_it->pc->source_location() == it->pc->source_location())
    return true;

  if(it->is_goto() && it->pc->condition().is_true())
    return true;

  const source_locationt &source_location = it->pc->source_location();

  if(source_location.is_nil() ||
     source_location.get_file().empty() ||
     source_location.is_built_in() ||
     source_location.get_line().empty())
  {
    const irep_idt id = source_location.get_function();
    // Do not filter out assertions in functions the name of which starts with
    // CPROVER_PREFIX, because we need to maintain those as violation nodes:
    // these are assertions generated, for examples, for memory leaks.
    if(!has_prefix(id2string(id), CPROVER_PREFIX) || !it->is_assert())
      return true;
  }

  return false;
}

static bool contains_symbol_prefix(const exprt &expr, const std::string &prefix)
{
  if(
    expr.id() == ID_symbol &&
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
  unsigned int max_thread_idx = 0;
  bool trace_has_violation = false;
  for(goto_tracet::stepst::const_iterator it = goto_trace.steps.begin();
      it != goto_trace.steps.end();
      ++it)
  {
    if(it->thread_nr > max_thread_idx)
      max_thread_idx = it->thread_nr;
    if(it->is_assert() && !it->cond_value)
      trace_has_violation = true;
  }

  graphml.key_values["sourcecodelang"]="C";

  const graphmlt::node_indext sink=graphml.add_node();
  graphml[sink].node_name="sink";
  graphml[sink].is_violation=false;
  graphml[sink].has_invariant=false;

  if(max_thread_idx > 0 && trace_has_violation)
  {
    std::vector<graphmlt::node_indext> nodes;

    for(unsigned int i = 0; i <= max_thread_idx + 1; ++i)
    {
      nodes.push_back(graphml.add_node());
      graphml[nodes.back()].node_name = "N" + std::to_string(i);
      graphml[nodes.back()].is_violation = i == max_thread_idx + 1;
      graphml[nodes.back()].has_invariant = false;
    }

    for(auto it = nodes.cbegin(); std::next(it) != nodes.cend(); ++it)
    {
      xmlt edge("edge");
      edge.set_attribute("source", graphml[*it].node_name);
      edge.set_attribute("target", graphml[*std::next(it)].node_name);
      const auto thread_id = std::distance(nodes.cbegin(), it);
      xmlt &data = edge.new_element("data");
      data.set_attribute("key", "createThread");
      data.data = std::to_string(thread_id);
      if(thread_id == 0)
      {
        xmlt &data = edge.new_element("data");
        data.set_attribute("key", "enterFunction");
        data.data = "main";
      }
      graphml[*std::next(it)].in[*it].xml_node = edge;
      graphml[*it].out[*std::next(it)].xml_node = edge;
    }

    // we do not provide any further details as CPAchecker does not seem to
    // handle more detailed concurrency witnesses
    return;
  }

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
    if(
      next != goto_trace.steps.end() &&
      next->type == goto_trace_stept::typet::ASSIGNMENT &&
      it->full_lhs == next->full_lhs &&
      it->pc->source_location() == next->pc->source_location())
    {
      step_to_node[it->step_nr]=sink;

      continue;
    }

    prev_it=it;

    const source_locationt &source_location = it->pc->source_location();

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

  unsigned thread_id = 0;

  // build edges
  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      ) // no ++it
  {
    const std::size_t from=step_to_node[it->step_nr];

    // no outgoing edges from sinks or violation nodes
    if(from == sink || graphml[from].is_violation)
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
      xmlt edge(
        "edge",
        {{"source", graphml[from].node_name},
         {"target", graphml[to].node_name}},
        {});

      {
        xmlt &data_f = edge.new_element("data");
        data_f.set_attribute("key", "originfile");
        data_f.data = id2string(graphml[from].file);

        xmlt &data_l = edge.new_element("data");
        data_l.set_attribute("key", "startline");
        data_l.data = id2string(graphml[from].line);

        xmlt &data_t = edge.new_element("data");
        data_t.set_attribute("key", "threadId");
        data_t.data = std::to_string(it->thread_nr);
      }

      const auto lhs_object = it->get_lhs_object();
      if(
        it->type == goto_trace_stept::typet::ASSIGNMENT &&
        lhs_object.has_value())
      {
        const std::string &lhs_id = id2string(lhs_object->get_identifier());
        if(lhs_id.find("pthread_create::thread") != std::string::npos)
        {
          xmlt &data_t = edge.new_element("data");
          data_t.set_attribute("key", "createThread");
          data_t.data = std::to_string(++thread_id);
        }
        else if(
          !contains_symbol_prefix(
            it->full_lhs_value, SYMEX_DYNAMIC_PREFIX "dynamic_object") &&
          !contains_symbol_prefix(
            it->full_lhs, SYMEX_DYNAMIC_PREFIX "dynamic_object") &&
          lhs_id.find("thread") == std::string::npos &&
          lhs_id.find("mutex") == std::string::npos &&
          (!it->full_lhs_value.is_constant() ||
           !it->full_lhs_value.has_operands() ||
           !has_prefix(
             id2string(
               to_multi_ary_expr(it->full_lhs_value).op0().get(ID_value)),
             "INVALID-")))
        {
          xmlt &val = edge.new_element("data");
          val.set_attribute("key", "assumption");

          code_assignt assign{it->full_lhs, it->full_lhs_value};
          val.data = convert_assign_rec(lhs_id, assign);

          xmlt &val_s = edge.new_element("data");
          val_s.set_attribute("key", "assumption.scope");
          irep_idt function_id = it->function_id;
          const symbolt *symbol_ptr = nullptr;
          if(!ns.lookup(lhs_id, symbol_ptr) && symbol_ptr->is_parameter)
          {
            function_id = lhs_id.substr(0, lhs_id.find("::"));
          }
          val_s.data = id2string(function_id);

          if(has_prefix(val.data, "\\result ="))
          {
            xmlt &val_f = edge.new_element("data");
            val_f.set_attribute("key", "assumption.resultfunction");
            val_f.data = id2string(it->function_id);
          }
        }
      }
      else if(it->type == goto_trace_stept::typet::GOTO && it->pc->is_goto())
      {
      }

      graphml[to].in[from].xml_node = edge;
      graphml[from].out[to].xml_node = edge;

      break;
    }

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
    const source_locationt &source_location = it->source.pc->source_location();

    if(
      it->hidden ||
      (!it->is_assignment() && !it->is_goto() && !it->is_assert()) ||
      (it->is_goto() && it->source.pc->condition().is_true()) ||
      source_location.is_nil() || source_location.is_built_in() ||
      source_location.get_line().empty())
    {
      step_to_node[step_nr]=sink;

      continue;
    }

    // skip declarations followed by an immediate assignment
    symex_target_equationt::SSA_stepst::const_iterator next=it;
    ++next;
    if(
      next != equation.SSA_steps.end() && next->is_assignment() &&
      it->ssa_full_lhs == next->ssa_full_lhs &&
      it->source.pc->source_location() == next->source.pc->source_location())
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
      xmlt edge(
        "edge",
        {{"source", graphml[from].node_name},
         {"target", graphml[to].node_name}},
        {});

      {
        xmlt &data_f = edge.new_element("data");
        data_f.set_attribute("key", "originfile");
        data_f.data = id2string(graphml[from].file);

        xmlt &data_l = edge.new_element("data");
        data_l.set_attribute("key", "startline");
        data_l.data = id2string(graphml[from].line);
      }

      if(
        (it->is_assignment() || it->is_decl()) && it->ssa_rhs.is_not_nil() &&
        it->ssa_full_lhs.is_not_nil())
      {
        irep_idt identifier = it->ssa_lhs.get_object_name();

        graphml[to].has_invariant = true;
        code_assignt assign(it->ssa_lhs, it->ssa_rhs);
        graphml[to].invariant = convert_assign_rec(identifier, assign);
        graphml[to].invariant_scope = id2string(it->source.function_id);
      }

      graphml[to].in[from].xml_node = edge;
      graphml[from].out[to].xml_node = edge;

      break;
    }

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
