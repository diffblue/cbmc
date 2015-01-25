/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: January 2015

\*******************************************************************/

#include <util/config.h>
#include <util/i2string.h>
#include <util/arith_tools.h>
#include <util/prefix.h>

#include <goto-symex/ssa_expr.h>

#include "graphml_goto_trace.h"

/*******************************************************************\

Function: remove_l0_l1

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void remove_l0_l1(exprt &expr)
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

/*******************************************************************\

Function: convert_assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::string convert_assign_rec(
  const namespacet &ns,
  const irep_idt &identifier,
  const code_assignt &assign)
{
  std::string result;

  if(assign.rhs().id()==ID_array)
  {
    const array_typet &type=
      to_array_type(ns.follow(assign.rhs().type()));

    unsigned i=0;
    forall_operands(it, assign.rhs())
    {
      index_exprt index(
          assign.lhs(),
          from_integer(i++, signedbv_typet(config.ansi_c.pointer_width)),
          type.subtype());
      if(!result.empty()) result+=' ';
      result+=convert_assign_rec(ns, identifier, code_assignt(index, *it));
    }
  }
  else if(assign.rhs().id()==ID_struct ||
          assign.rhs().id()==ID_union)
  {
    const struct_union_typet &type=
      to_struct_union_type(ns.follow(assign.lhs().type()));
    const struct_union_typet::componentst &components=
      type.components();

    struct_union_typet::componentst::const_iterator c_it=
      components.begin();
    forall_operands(it, assign.rhs())
    {
      if(c_it->type().id()==ID_code ||
         c_it->get_is_padding() ||
         // for some reason #is_padding gets lost in *some* cases
         has_prefix(id2string(c_it->get_name()), "$pad"))
      {
        ++c_it;
        continue;
      }

      assert(c_it!=components.end());
      member_exprt member(
          assign.lhs(),
          c_it->get_name(),
          it->type());
      if(!result.empty()) result+=' ';
      result+=convert_assign_rec(ns, identifier, code_assignt(member, *it));
      ++c_it;
    }
  }
  else
  {
    exprt clean_rhs=assign.rhs();
    remove_l0_l1(clean_rhs);

    result=from_expr(ns, identifier, assign.lhs())+" = "+
           from_expr(ns, identifier, clean_rhs)+";";
  }

  return result;
}

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  graphmlt &graphml)
{
  const unsigned sink=graphml.add_node();
  graphml[sink].node_name="sink";
  graphml[sink].thread_nr=0;
  graphml[sink].is_violation=false;

  // prepare all nodes
  std::map<unsigned, unsigned> pc_to_node;
  // step numbers start at 1
  std::vector<unsigned> step_to_node(goto_trace.steps.size()+1, 0);

  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
  {
    const source_locationt &source_location=it->pc->source_location;

    if(it->hidden ||
       source_location.is_nil() ||
       source_location.get_file().empty() ||
       source_location.get_file()=="<built-in-additions>" ||
       source_location.get_line().empty())
    {
      step_to_node[it->step_nr]=sink;

      continue;
    }

    std::pair<std::map<unsigned, unsigned>::iterator, bool> entry=
      pc_to_node.insert(std::make_pair(it->pc->location_number, 0));
    if(entry.second)
    {
      entry.first->second=graphml.add_node();
      graphml[entry.first->second].node_name=i2string(entry.first->first);
      graphml[entry.first->second].file=source_location.get_file();
      graphml[entry.first->second].line=source_location.get_line();
      graphml[entry.first->second].thread_nr=it->thread_nr;
      graphml[entry.first->second].is_violation=
        it->type==goto_trace_stept::ASSERT && !it->cond_value;
    }

    step_to_node[it->step_nr]=entry.first->second;
  }

  // build edges
  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
  {
    const unsigned from=step_to_node[it->step_nr];

    if(from==sink) continue;

    goto_tracet::stepst::const_iterator next=it;
    for(++next; next!=goto_trace.steps.end() && next->hidden; ++next) ;
    const unsigned to=
      next==goto_trace.steps.end()?
      sink:step_to_node[next->step_nr];

    switch(it->type)
    {
    case goto_trace_stept::DECL:
      // skip declarations followed by an immediate assignment
      if(next->type==goto_trace_stept::ASSIGNMENT &&
         it->full_lhs==next->full_lhs)
        continue;
    case goto_trace_stept::ASSIGNMENT:
    case goto_trace_stept::ASSERT:
    case goto_trace_stept::LOCATION:
    case goto_trace_stept::FUNCTION_CALL:
      if(it->type!=goto_trace_stept::LOCATION ||
         from!=to)
      {
        xmlt edge("edge");
        edge.set_attribute("source", graphml[from].node_name);
        edge.set_attribute("target", graphml[to].node_name);

        {
          xmlt &data_f=edge.new_element("data");
          data_f.set_attribute("key", "originfile");
          data_f.data='"'+id2string(graphml[from].file)+'"';

          xmlt &data_l=edge.new_element("data");
          data_l.set_attribute("key", "originline");
          data_l.data=id2string(graphml[from].line);
        }

        if((it->type==goto_trace_stept::ASSIGNMENT ||
            it->type==goto_trace_stept::DECL) &&
           it->lhs_object_value.is_not_nil() &&
           it->full_lhs.is_not_nil())
        {
          irep_idt identifier=it->lhs_object.get_identifier();

          xmlt &val=edge.new_element("data");
          val.set_attribute("key", "assumption");
          code_assignt assign(it->lhs_object, it->lhs_object_value);
          val.data=convert_assign_rec(ns, identifier, assign);
        }
        else if(it->type==goto_trace_stept::LOCATION &&
                it->pc->is_goto())
        {
          xmlt &val=edge.new_element("data");
          val.set_attribute("key", "sourcecode");
          const std::string cond=from_expr(ns, "", it->cond_expr);
          const std::string neg_cond=
            from_expr(ns, "", not_exprt(it->cond_expr));
          val.data="["+(it->goto_taken ? cond : neg_cond)+"]";

          xmlt edge2("edge");
          edge2.set_attribute("source", graphml[from].node_name);
          edge2.set_attribute("target", graphml[sink].node_name);

          xmlt &data_f2=edge2.new_element("data");
          data_f2.set_attribute("key", "originfile");
          data_f2.data='"'+id2string(graphml[from].file)+'"';

          xmlt &data_l2=edge2.new_element("data");
          data_l2.set_attribute("key", "originline");
          data_l2.data=id2string(graphml[from].line);

          xmlt &val2=edge2.new_element("data");
          val2.set_attribute("key", "sourcecode");
          val2.data="["+(it->goto_taken ? neg_cond : cond)+"]";

          graphml[sink].in[from].xml_node=edge2;
          graphml[from].out[sink].xml_node=edge2;
        }

        graphml[to].in[from].xml_node=edge;
        graphml[from].out[to].xml_node=edge;
      }
      break;

    case goto_trace_stept::FUNCTION_RETURN:
    case goto_trace_stept::ASSUME:
    case goto_trace_stept::INPUT:
    case goto_trace_stept::OUTPUT:
    case goto_trace_stept::SHARED_READ:
    case goto_trace_stept::SHARED_WRITE:
    case goto_trace_stept::SPAWN:
    case goto_trace_stept::MEMORY_BARRIER:
    case goto_trace_stept::ATOMIC_BEGIN:
    case goto_trace_stept::ATOMIC_END:
    case goto_trace_stept::DEAD:
    case goto_trace_stept::CONSTRAINT:
    case goto_trace_stept::NONE:
        ; /* ignore */
    }
  }
}
