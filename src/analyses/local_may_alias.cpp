/*******************************************************************\

Module: Field-insensitive, location-sensitive may-alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iterator>
#include <algorithm>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/expr_util.h>

#include <ansi-c/c_types.h>
#include <langapi/language_util.h>

#include "local_may_alias.h"

/*******************************************************************\

Function: local_may_aliast::destt::merge

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool local_may_aliast::destt::merge(const destt &src)
{
  bool result=false;

  std::size_t old_size=objects.size();
  objects.insert(src.objects.begin(), src.objects.end());

  if(objects.size()!=old_size)
    result=true;

  return result;
}

/*******************************************************************\

Function: local_may_aliast::loc_infot::merge

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool local_may_aliast::loc_infot::merge(const loc_infot &src)
{
  bool result=false;
  
  points_tot::iterator dest_it=points_to.begin();

  for(points_tot::const_iterator
      src_it=src.points_to.begin();
      src_it!=src.points_to.end();
      ) // no it++
  {
    if(dest_it==points_to.end() || 
       src_it->first<dest_it->first)
    {
      points_to.insert(dest_it, *src_it);
      result=true;
      src_it++;
      continue;
    }
    else if(dest_it->first<src_it->first)
    {
      dest_it++;
      continue;
    }
    
    assert(dest_it->first==src_it->first);
    
    if(dest_it->second.merge(src_it->second))
      result=true;

    dest_it++;
    src_it++;
  }
  
  return result;
}

/*******************************************************************\

Function: local_may_aliast::is_tracked

  Inputs:

 Outputs: return 'true' iff we track the object with given
          identifier

 Purpose:

\*******************************************************************/

bool local_may_aliast::is_tracked(const irep_idt &identifier) const
{
  localst::locals_mapt::const_iterator it=locals.locals_map.find(identifier);
  if(it==locals.locals_map.end()) return false;
  if(it->second.id()!=ID_pointer) return false;
  if(dirty(identifier)) return false;
  return true;
}

/*******************************************************************\

Function: local_may_aliast::assign

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void local_may_aliast::assign_lhs(
  const exprt &lhs,
  const exprt &rhs,
  const loc_infot &loc_info_src,
  loc_infot &loc_info_dest)
{
  if(lhs.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(lhs).get_identifier();

    if(is_tracked(identifier))
    {
      unsigned dest_pointer=pointers.number(identifier);
      destt &dest_set=loc_info_dest.points_to[dest_pointer];
      dest_set.clear();
      get_rec(dest_set, rhs, loc_info_src);
    }
  }
  else if(lhs.id()==ID_dereference)
  {
  }
  else if(lhs.id()==ID_index)
  {
    assign_lhs(to_index_expr(lhs).array(), rhs, loc_info_src, loc_info_dest);
  }
  else if(lhs.id()==ID_member)
  {
    assign_lhs(to_member_expr(lhs).struct_op(), rhs, loc_info_src, loc_info_dest);
  }
  else if(lhs.id()==ID_typecast)
  {
    assign_lhs(to_typecast_expr(lhs).op(), rhs, loc_info_src, loc_info_dest);
  }
  else if(lhs.id()==ID_if)
  {
    assign_lhs(to_if_expr(lhs).true_case(), rhs, loc_info_src, loc_info_dest);
    assign_lhs(to_if_expr(lhs).false_case(), rhs, loc_info_src, loc_info_dest);
  }
}
 
/*******************************************************************\

Function: local_may_aliast::get

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

std::set<exprt> local_may_aliast::get(
  const goto_programt::const_targett t,
  const exprt &rhs) const
{
  local_cfgt::loc_mapt::const_iterator loc_it=cfg.loc_map.find(t);
  
  assert(loc_it!=cfg.loc_map.end());
  
  const loc_infot &loc_info_src=loc_infos[loc_it->second];
  
  destt result_tmp;
  get_rec(result_tmp, rhs, loc_info_src);

  std::set<exprt> result;

  for(std::set<unsigned>::const_iterator
      it=result_tmp.objects.begin();
      it!=result_tmp.objects.end();
      it++)
  {
    result.insert(objects[*it]);
  }  
  
  return result;
}

/*******************************************************************\

Function: local_may_aliast::aliases

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool local_may_aliast::aliases(
  const goto_programt::const_targett t,
  const exprt &src1, const exprt &src2) const
{
  local_cfgt::loc_mapt::const_iterator loc_it=cfg.loc_map.find(t);
  
  assert(loc_it!=cfg.loc_map.end());
  
  const loc_infot &loc_info_src=loc_infos[loc_it->second];
  
  destt tmp1, tmp2;
  get_rec(tmp1, src1, loc_info_src);
  get_rec(tmp2, src2, loc_info_src);

  if(tmp1.objects.find(unknown_object)!=tmp1.objects.end() ||
     tmp2.objects.find(unknown_object)!=tmp2.objects.end())
    return true;

  std::list<unsigned> result;
  
  std::set_intersection(
    tmp1.objects.begin(), tmp1.objects.end(),
    tmp2.objects.begin(), tmp2.objects.end(),
    std::back_inserter(result));
  
  return !result.empty();
}

/*******************************************************************\

Function: local_may_aliast::get_rec

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void local_may_aliast::get_rec(
  destt &dest,
  const exprt &rhs,
  const loc_infot &loc_info_src) const
{
  if(rhs.id()==ID_constant)
  {
    if(rhs.is_zero())
      dest.objects.insert(objects.number(exprt(ID_null_object)));
    else
      dest.objects.insert(objects.number(exprt(ID_integer_address_object)));
  }
  else if(rhs.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(rhs).get_identifier();
    if(is_tracked(identifier))
    {
      unsigned src_pointer=pointers.number(identifier);
      points_tot::const_iterator src_it=loc_info_src.points_to.find(src_pointer);
      if(src_it!=loc_info_src.points_to.end())
      {
        const std::set<unsigned> &src=src_it->second.objects;
        dest.objects.insert(src.begin(), src.end());
      }
    }
    else
      dest.objects.insert(unknown_object);
  }
  else if(rhs.id()==ID_address_of)
  {
    const exprt &object=to_address_of_expr(rhs).object();
    
    if(object.id()==ID_symbol)
    {
      unsigned object_nr=objects.number(object);
      dest.objects.insert(object_nr);
    }
    else if(object.id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(object);
      if(index_expr.array().id()==ID_symbol)
      {
        index_exprt tmp=index_expr;
        tmp.index()=gen_zero(index_type());
        dest.objects.insert(objects.number(tmp));
      }
      else
        dest.objects.insert(unknown_object);
    }
    else
      dest.objects.insert(unknown_object);
  }
  else if(rhs.id()==ID_typecast)
  {
    get_rec(dest, to_typecast_expr(rhs).op(), loc_info_src);
  }
  else if(rhs.id()==ID_plus)
  {
    if(rhs.operands().size()>=3)
    {
      get_rec(dest, make_binary(rhs), loc_info_src);
    }
    else if(rhs.operands().size()==2)
    {
      // one must be pointer, one an integer
      if(rhs.op0().type().id()==ID_pointer)
      {
        get_rec(dest, rhs.op0(), loc_info_src);
      }
      else if(rhs.op1().type().id()==ID_pointer)
      {
        get_rec(dest, rhs.op1(), loc_info_src);
      }
      else
        dest.objects.insert(unknown_object);
    }
    else
      dest.objects.insert(unknown_object);
  }
  else if(rhs.id()==ID_minus)
  {
    if(rhs.op0().type().id()==ID_pointer)
    {
      get_rec(dest, rhs.op0(), loc_info_src);
    }
    else
      dest.objects.insert(unknown_object);
  }
  else if(rhs.id()==ID_member)
  {
    dest.objects.insert(unknown_object);
  }
  else if(rhs.id()==ID_index)
  {
    dest.objects.insert(unknown_object);
  }
  else if(rhs.id()==ID_dereference)
  {
    dest.objects.insert(unknown_object);
  }
  else if(rhs.id()==ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(rhs);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_malloc)
    {
      dest.objects.insert(objects.number(exprt(ID_dynamic_object)));
    }
    else
      dest.objects.insert(unknown_object);
  }
  else
    dest.objects.insert(unknown_object);
}
 
/*******************************************************************\

Function: local_may_aliast::build

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void local_may_aliast::build(const goto_functiont &goto_function)
{
  if(cfg.nodes.empty()) return;

  work_queuet work_queue;
  work_queue.push(0);  
  
  unknown_object=objects.number(exprt(ID_unknown));
  
  loc_infos.resize(cfg.nodes.size());
  
  // feed in sufficiently bad defaults
  for(code_typet::parameterst::const_iterator
      it=goto_function.type.parameters().begin();
      it!=goto_function.type.parameters().end();
      it++)
  {
    const irep_idt &identifier=it->get_identifier();
    if(is_tracked(identifier))
      loc_infos[0].points_to[pointers.number(identifier)].objects.insert(unknown_object);
  }

  for(localst::locals_mapt::const_iterator
      l_it=locals.locals_map.begin();
      l_it!=locals.locals_map.end();
      l_it++)
  {
    if(is_tracked(l_it->first))
      loc_infos[0].points_to[pointers.number(l_it->first)].objects.insert(unknown_object);
  }

  while(!work_queue.empty())
  {
    local_cfgt::node_nrt loc_nr=work_queue.top();
    const local_cfgt::nodet &node=cfg.nodes[loc_nr];
    const goto_programt::instructiont &instruction=*node.t;
    work_queue.pop();
    
    const loc_infot &loc_info_src=loc_infos[loc_nr];
    loc_infot loc_info_dest=loc_infos[loc_nr];
    
    switch(instruction.type)
    {
    case ASSIGN:
      {
        const code_assignt &code_assign=to_code_assign(instruction.code);
        assign_lhs(code_assign.lhs(), code_assign.rhs(), loc_info_src, loc_info_dest);
      }
      break;

    case DECL:
      {
        const code_declt &code_decl=to_code_decl(instruction.code);
        assign_lhs(code_decl.symbol(), nil_exprt(), loc_info_src, loc_info_dest);
      }
      break;

    case DEAD:
      {
        const code_deadt &code_dead=to_code_dead(instruction.code);
        assign_lhs(code_dead.symbol(), nil_exprt(), loc_info_src, loc_info_dest);
      }
      break;

    case FUNCTION_CALL:
      {
        const code_function_callt &code_function_call=to_code_function_call(instruction.code);
        if(code_function_call.lhs().is_not_nil())
          assign_lhs(code_function_call.lhs(), nil_exprt(), loc_info_src, loc_info_dest);
      }
      break;

    default:;
    }

    for(local_cfgt::successorst::const_iterator
        it=node.successors.begin();
        it!=node.successors.end();
        it++)
    {
      if(loc_infos[*it].merge(loc_info_dest))
        work_queue.push(*it);
    }
  }
}

/*******************************************************************\

Function: local_may_aliast::output

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void local_may_aliast::output(
  std::ostream &out,
  const goto_functiont &goto_function,
  const namespacet &ns) const
{
  unsigned l=0;

  forall_goto_program_instructions(i_it, goto_function.body)
  {
    out << "**** " << i_it->source_location << "\n";

    const loc_infot &loc_info=loc_infos[l];

    for(points_tot::const_iterator
        p_it=loc_info.points_to.begin();
        p_it!=loc_info.points_to.end();
        p_it++)
    {
      out << "  " << pointers[p_it->first] << " = { ";

      for(std::set<unsigned>::const_iterator
          s_it=p_it->second.objects.begin();
          s_it!=p_it->second.objects.end();
          s_it++)
      {
        if(s_it!=p_it->second.objects.begin()) out << ", ";
        out << from_expr(ns, "", objects[*s_it]);
      }
        
      out << " }";
      
      out << "\n";
    }

    out << "\n";
    goto_function.body.output_instruction(ns, "", out, i_it);
    out << "\n";
    
    l++;
  }
}

