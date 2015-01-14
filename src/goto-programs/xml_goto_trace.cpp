/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

#include <cassert>

#include <util/xml_expr.h>
#include <util/i2string.h>
#include <util/symbol.h>
#include <util/config.h>
#include <util/arith_tools.h>

#include <ansi-c/printf_formatter.h>
#include <langapi/language_util.h>

#include "xml_goto_trace.h"

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  xmlt &dest)
{
  dest=xmlt("goto_trace");
  
  source_locationt previous_source_location;

  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
  {
    const source_locationt &source_location=it->pc->source_location;

    xmlt xml_location;
    if(source_location.is_not_nil() && source_location.get_file()!="")
      xml_location=xml(source_location);
    
    switch(it->type)
    {
    case goto_trace_stept::ASSERT:
      if(!it->cond_value)
      {
        irep_idt property_id;
        
        if(it->pc->is_assert())
          property_id=source_location.get_property_id();
        else if(it->pc->is_goto()) // unwinding, we suspect
        {
          property_id=
            id2string(it->pc->source_location.get_function())+".unwind."+
            i2string(it->pc->loop_number);
        }
      
        xmlt &xml_failure=dest.new_element("failure");
        #if 0
        xml_failure.new_element("reason").data=id2string(it->comment);
        xml_failure.new_element("step_nr").data=i2string(it->step_nr);        
        xml_failure.new_element("thread").data=i2string(it->thread_nr);
        #endif

        // new, to replace above
        xml_failure.set_attribute("thread", i2string(it->thread_nr));
        xml_failure.set_attribute("step_nr", i2string(it->step_nr));
        xml_failure.set_attribute("reason", id2string(it->comment));
        xml_failure.set_attribute("property", id2string(property_id));

        if(xml_location.name!="")
          xml_failure.new_element().swap(xml_location);
      }
      break;
      
    case goto_trace_stept::ASSIGNMENT:
    case goto_trace_stept::DECL:
      {
        irep_idt identifier=it->lhs_object.get_identifier();
        xmlt &xml_assignment=dest.new_element("assignment");

        if(xml_location.name!="")
          xml_assignment.new_element().swap(xml_location);

        std::string value_string, binary_string, type_string,
                    full_lhs_string, full_lhs_value_string;
        
        if(it->lhs_object_value.is_not_nil())
          value_string=from_expr(ns, identifier, it->lhs_object_value);

        if(it->full_lhs.is_not_nil())
          full_lhs_string=from_expr(ns, identifier, it->full_lhs);

        if(it->full_lhs_value.is_not_nil())
          full_lhs_value_string=from_expr(ns, identifier, it->full_lhs_value);

        if(it->lhs_object_value.type().is_not_nil())
          type_string=from_type(ns, identifier, it->lhs_object_value.type());

        const symbolt *symbol;
        irep_idt base_name, display_name;

        if(!ns.lookup(identifier, symbol))
        {
          base_name=symbol->base_name;
          display_name=symbol->display_name();
          if(type_string=="")
            type_string=from_type(ns, identifier, symbol->type);

          xml_assignment.set_attribute("mode", id2string(symbol->mode));
        }

        #if 0
        xml_assignment.new_element("thread").data=i2string(it->thread_nr);
        xml_assignment.new_element("identifier").data=id2string(identifier);
        xml_assignment.new_element("base_name").data=id2string(base_name);
        xml_assignment.new_element("display_name").data=id2string(display_name);
        xml_assignment.new_element("step_nr").data=i2string(it->step_nr);
        #endif

        xml_assignment.new_element("type").data=type_string;
        xml_assignment.new_element("full_lhs").data=full_lhs_string;
        xml_assignment.new_element("full_lhs_value").data=full_lhs_value_string;
        xml_assignment.new_element("value").data=value_string;
        
        // new, to replace above
        xml_assignment.set_attribute("thread", i2string(it->thread_nr));
        xml_assignment.set_attribute("identifier", id2string(identifier));
        xml_assignment.set_attribute("base_name", id2string(base_name));
        xml_assignment.set_attribute("display_name", id2string(display_name));
        xml_assignment.set_attribute("step_nr", i2string(it->step_nr));

        if(it->lhs_object_value.is_not_nil())
          xml_assignment.new_element("value_expression").new_element(xml(it->lhs_object_value, ns));
      }
      break;
      
    case goto_trace_stept::OUTPUT:
      {
        printf_formattert printf_formatter(ns);
        printf_formatter(id2string(it->format_string), it->io_args);
        std::string text=printf_formatter.as_string();
        xmlt &xml_output=dest.new_element("output");
        
        #if 0
        xml_output.new_element("step_nr").data=i2string(it->step_nr);
        xml_output.new_element("thread").data=i2string(it->thread_nr);
        #endif
        
        xml_output.new_element("text").data=text;

        // new, to replace above
        xml_output.set_attribute("thread", i2string(it->thread_nr));
        xml_output.set_attribute("step_nr", i2string(it->step_nr));

        if(xml_location.name!="")
          xml_output.new_element().swap(xml_location);

        for(std::list<exprt>::const_iterator
            l_it=it->io_args.begin();
            l_it!=it->io_args.end();
            l_it++)
        {
          xml_output.new_element("value").data=from_expr(ns, "", *l_it);
          xml_output.new_element("value_expression").
            new_element(xml(*l_it, ns));
        }
      }
      break;
      
    case goto_trace_stept::INPUT:
      {
        xmlt &xml_input=dest.new_element("input");
        xml_input.new_element("input_id").data=id2string(it->io_id);
        
        #if 0
        xml_input.new_element("step_nr").data=i2string(it->step_nr);
        xml_input.new_element("thread").data=i2string(it->thread_nr);
        #endif

        // new, to replace above
        xml_input.set_attribute("thread", i2string(it->thread_nr));
        xml_input.set_attribute("step_nr", i2string(it->step_nr));
        
        for(std::list<exprt>::const_iterator
            l_it=it->io_args.begin();
            l_it!=it->io_args.end();
            l_it++)
        {
          xml_input.new_element("value").data=from_expr(ns, "", *l_it);
          xml_input.new_element("value_expression").
            new_element(xml(*l_it, ns));
        }
            
        if(xml_location.name!="")
          xml_input.new_element().swap(xml_location);
      }
      break;
      
    case goto_trace_stept::FUNCTION_CALL:
    case goto_trace_stept::FUNCTION_RETURN:
      {
        std::string tag=
          (it->type==goto_trace_stept::FUNCTION_CALL)?"function_call":"function_return";
        xmlt &xml_call_return=dest.new_element(tag);
        
        #if 0
        xml_call_return.new_element("step_nr").data=i2string(it->step_nr);
        xml_call_return.new_element("thread").data=i2string(it->thread_nr);
        #endif

        // new, to replace above
        xml_call_return.set_attribute("thread", i2string(it->thread_nr));
        xml_call_return.set_attribute("step_nr", i2string(it->step_nr));

        const symbolt &symbol=ns.lookup(it->identifier);
        xmlt &xml_function=xml_call_return.new_element("function");
        xml_function.set_attribute("display_name", id2string(symbol.display_name()));
        xml_function.set_attribute("identifier", id2string(it->identifier));
        xml_function.new_element()=xml(symbol.location);

        if(xml_location.name!="")
          xml_call_return.new_element().swap(xml_location);
      }
      break;
      
    default:
      if(source_location!=previous_source_location)
      {
        // just the source location
        if(xml_location.name!="")
        {
          xmlt &xml_location_only=dest.new_element("location-only");
          
          #if 0
          xml_location_only.new_element("step_nr").data=i2string(it->step_nr);
          xml_location_only.new_element("thread").data=i2string(it->thread_nr);
          #endif

          // new, to replace above
          xml_location_only.set_attribute("thread", i2string(it->thread_nr));
          xml_location_only.set_attribute("step_nr", i2string(it->step_nr));

          xml_location_only.new_element().swap(xml_location);
        }
      }
    }

    if(source_location.is_not_nil() && source_location.get_file()!="")
      previous_source_location=source_location;
  }
}

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void convert_assign_rec(
  const namespacet &ns,
  const irep_idt &identifier,
  const code_assignt &assign,
  std::string &dest)
{
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
      convert_assign_rec(ns, identifier, code_assignt(index, *it), dest);
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
         c_it->get_is_padding())
      {
        ++c_it;
        continue;
      }

      assert(c_it!=components.end());
      member_exprt member(
          assign.lhs(),
          c_it->get_name(),
          it->type());
      convert_assign_rec(ns, identifier, code_assignt(member, *it), dest);
      ++c_it;
    }
  }
  else
  {
    if(!dest.empty()) dest+=' ';
    dest+=from_expr(ns, identifier, assign.lhs())+" = "+
          from_expr(ns, identifier, assign.rhs())+";";
  }
}

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
#if 0
  const cfg_baset<empty_cfg_nodet> &cfg,
#endif
  graphmlt &graphml)
{
  const unsigned sink=graphml.add_node();
  graphml[sink].node_name="sink";
  graphml[sink].thread_nr=0;
  graphml[sink].is_violation=false;

  // prepare all nodes
  std::map<unsigned, unsigned> pc_to_node;
  std::vector<unsigned> step_to_node(goto_trace.steps.size(), 0);

  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
  {
    const source_locationt &source_location=it->pc->source_location;

    if(source_location.is_nil() ||
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
    ++next;
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

        /*
        xmlt &data=edge.new_element("data");
        data.set_attribute("key", "tokens");
        data.data=graphml[from].node_name;
        if(graphml[from].node_name!=graphml[to].node_name &&
           to!=sink)
          data.data+=","+graphml[to].line;
        */
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
          convert_assign_rec(ns, identifier, assign, val.data);
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

          /*
          xmlt &data2=edge2.new_element("data");
          data2.set_attribute("key", "tokens");
          data2.data=graphml[from].node_name;

          const locationt &loc=it->cond_expr.find_location();
          if(loc.is_not_nil())
          {
            data.data+=","+id2string(loc.get_line());
            data2.data+=","+id2string(loc.get_line());
          }
          */
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

#if 0
  assert(!previous_line.empty());

  graph<visited_nodet<empty_edget> > reachable;

  reachable.resize(cfg.size());
  for(unsigned i=0; i<cfg.size(); ++i)
  {
    const cfg_baset<empty_cfg_nodet>::nodet &node=cfg[i];

    for(cfg_baset<empty_cfg_nodet>::edgest::const_iterator
        it=node.out.begin();
        it!=node.out.end();
        ++it)
      reachable.add_edge(i, it->first);
  }

  assert(!goto_trace.steps.empty());
  goto_programt::const_targett assertion=goto_trace.steps.back().pc;

  cfg_baset<empty_cfg_nodet>::entry_mapt::const_iterator cfg_entry=
    cfg.entry_map.find(assertion);
  assert(cfg_entry!=cfg.entry_map.end());

  reachable.visit_reachable(cfg_entry->second);

  irep_idt main_fn="c::main";
  if(!config.main.empty()) main_fn=config.main;

  for(unsigned i=0; i<cfg.size(); ++i)
  {
    const cfg_baset<empty_cfg_nodet>::nodet &node=cfg[i];
    const graph<visited_nodet<empty_edget> >::nodet &r_node=
      reachable[i];

    if(r_node.visited &&
       node.PC->function==main_fn)
    {
      const locationt &location=node.PC->location;

      if(location.is_nil() ||
         location.get_file().empty() ||
         location.get_file()=="<built-in-additions>" ||
         location.get_line().empty())
        continue;

      const irep_idt line=location.get_line();

      std::pair<std::map<irep_idt, unsigned>::iterator, bool> entry=
        line_to_node.insert(std::make_pair(line, 0));
      if(!entry.second)
        continue;

      entry.first->second=graphml.add_node();
      graphml[entry.first->second].node_name=id2string(line);

      std::map<irep_idt, unsigned>::const_iterator prev_entry=
        line_to_node.find(previous_line);
      assert(prev_entry!=line_to_node.end());

      xmlt edge("edge");
      edge.set_attribute("source", id2string(previous_line));
      edge.set_attribute("target", id2string(line));

      xmlt &data=edge.new_element("data");
      data.set_attribute("key", "tokens");
      data.data=id2string(previous_line);

      graphmlt::nodet &node=graphml[entry.first->second];
      node.is_sink=true;
      node.in[prev_entry->second].xml_node=edge;

      graphml[prev_entry->second].out[entry.first->second].xml_node=edge;
    }
  }
#endif
}
