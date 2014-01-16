/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <util/string2int.h>

#include "goto_symex.h"

unsigned goto_symext::nondet_count=0;
unsigned goto_symext::dynamic_counter=0;
unsigned goto_symext::heap_counter=0;

/*******************************************************************\

Function: goto_symext::do_simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::do_simplify(exprt &expr)
{
  if(options.get_bool_option("simplify"))
    simplify(expr, ns);
}

/*******************************************************************\

Function: goto_symext::replace_nondet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::replace_nondet(exprt &expr)
{
  if(expr.id()==ID_sideeffect &&
     expr.get(ID_statement)==ID_nondet)
  {
    exprt new_expr(ID_nondet_symbol, expr.type());
    new_expr.set(ID_identifier, "symex::nondet"+i2string(nondet_count++));
    new_expr.location()=expr.location();
    expr.swap(new_expr);
  }
  else
    Forall_operands(it, expr)
      replace_nondet(*it);
}

/*******************************************************************\

Function: goto_symext::replace_heap_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::replace_heap_member(exprt &expr)
{
  if(is_heap_type(expr.type()))
  {
    struct_typet struct_type;
    if(expr.type().id()==ID_pointer) struct_type = to_struct_type(ns.follow(expr.type().subtype()));
    else struct_type = to_struct_type(ns.follow(expr.type()));

    if(expr.id()==ID_member)
    {
      //    std::cout  << std::endl << "replace_heap_member: " << expr << std::endl;
      member_exprt struct_expr = to_member_expr(expr);
      irep_idt heap_id = make_heap_id(struct_type.get_tag());
      replace_heap_member(struct_expr.struct_op());
      heap_member_exprt hexpr(struct_expr.struct_op());
      hexpr.set_component_name(struct_expr.get_component_name());
      hexpr.location()=expr.location();
      hexpr.set_heap_id(heap_id);
      expr.swap(hexpr);
      return;
    }
    if(expr.id()==ID_symbol)
    {
      //TODO: perhaps generate a heap_symbol in future
      irep_idt heap_id = make_heap_id(struct_type.get_tag());
      expr.set(ID_new_heap_id,heap_id);
      irep_idt id = to_symbol_expr(expr).get_identifier();
      if(id2string(id).find("#")!=std::string::npos //TODO: dirty hack to add only L2 ids
         && heap_id_map.find(id)==heap_id_map.end()) { 
        heap_id_map[id] = heap_id;
	//        std::cout  << "add to heap_id_map0: " << id << ": " << heap_id << std::endl;
      }
      return;
    }
  }
  Forall_operands(it, expr)
    replace_heap_member(*it);
}

void goto_symext::update_heap_ids(irep_idt tag, irep_idt updated_id)
{
  irep_idt heap_id = make_heap_id(tag);
  std::string uid = id2string(updated_id);
  std::set<std::string> updated_ids;
  //assume: occur in ssa order
  unsigned upos = uid.find("#");
  std::string uids = upos!=std::string::npos ? uid.substr(0,upos) : uid;
  updated_ids.insert(uids);
  for(heap_id_mapt::iterator it1=heap_id_map.begin(); it1!=heap_id_map.end(); it1++)
  {
    std::string id1 = id2string(it1->first);
    unsigned pos1 = id1.find("#");
    unsigned n1 = safe_string2unsigned(id1.substr(pos1+1));
    id1 = id1.substr(0,pos1);
    if(updated_ids.find(id1)!=updated_ids.end()) continue;
    for(heap_id_mapt::iterator it2=heap_id_map.begin(); it2!=heap_id_map.end(); it2++)
    {
      std::string id2 = id2string(it2->first);
      unsigned pos2 = id2.find("#");
      if(id2.substr(0,pos2)==id1) 
      {
        unsigned n2 = safe_string2unsigned(id2.substr(pos1+1));
        if(n2>n1) n1 = n2;
      }
    }
    heap_id_map[id1+"#"+i2string(n1)] = heap_id;
    updated_ids.insert(id1);
    //    std::cout << "update heap_id: " << id1+"#"+i2string(n1) << " == " << heap_id << std::endl;
  }
}
