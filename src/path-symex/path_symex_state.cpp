/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/simplify_expr.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>
#include <util/i2string.h>

#include <ansi-c/c_types.h>

#include <pointer-analysis/dereference.h>

#include <goto-symex/adjust_float_expressions.h>

#include "path_symex_state.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

/*******************************************************************\

Function: initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_symex_statet initial_state(
  var_mapt &var_map,
  const locst &locs)
{
  path_symex_statet s(var_map, locs);
  
  // create one new thread
  path_symex_statet::threadt &thread=s.add_thread();
  thread.pc=locs.entry_loc; // set its PC
  s.set_current_thread(0);
  
  return s;
}

/*******************************************************************\

Function: path_symex_statet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_programt::const_targett path_symex_statet::get_instruction() const
{
  assert(current_thread<threads.size());
  return locs[threads[current_thread].pc].target;
}

/*******************************************************************\

Function: path_symex_statet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_statet::output(const threadt &thread, std::ostream &out) const
{
  out << "  PC: " << thread.pc << std::endl;
  out << "  Call stack:";
  for(call_stackt::const_iterator
      it=thread.call_stack.begin();
      it!=thread.call_stack.end();
      it++)
    out << " " << it->return_location << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: path_symex_statet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_statet::output(std::ostream &out) const
{
  for(unsigned t=0; t<threads.size(); t++)
  {
    out << "*** Thread " << t << std::endl;
    output(threads[t], out);
    out << std::endl;
  }
}

/*******************************************************************\

Function: path_symex_statet::get_var_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_symex_statet::var_statet &path_symex_statet::get_var_state(
  const var_mapt::var_infot &var_info)
{
  assert(current_thread<threads.size());

  var_valt &var_val=
    var_info.is_shared()?shared_vars:threads[current_thread].local_vars;
  if(var_val.size()<=var_info.number) var_val.resize(var_info.number+1);
  return var_val[var_info.number];
}

/*******************************************************************\

Function: path_symex_statet::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::read(const exprt &src, bool propagate)
{
  #ifdef DEBUG
  //std::cout << "path_symex_statet::read " << src.pretty() << std::endl;
  #endif
  
  exprt tmp1=adjust_float_expressions(src, var_map.ns);

  exprt tmp2=dereference_rec(tmp1, propagate);
  
  exprt tmp3=instantiate_rec(tmp2, propagate);
  
  exprt tmp4=simplify_expr(tmp3, var_map.ns);

  #ifdef DEBUG
  //std::cout << " ==> " << tmp.pretty() << std::endl;
  #endif

  return tmp4;
}

/*******************************************************************\

Function: path_symex_statet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::instantiate_rec(
  const exprt &src,
  bool propagate)
{
  #ifdef DEBUG
  std::cout << "instantiate_rec: "
            << from_expr(var_map.ns, "", src) << std::endl;
  #endif

  // check whether this is a symbol(.member|[index])*
  
  {
    exprt tmp_symbol_member_index=
      read_symbol_member_index_rec(src, "", src.type(), propagate);
  
    if(tmp_symbol_member_index.is_not_nil())
      return tmp_symbol_member_index; // yes!
  }
  
  if(src.id()==ID_address_of)
  {
    assert(src.operands().size()==1);
    exprt tmp=src;
    tmp.op0()=instantiate_rec_address(tmp.op0(), propagate);
    return tmp;
  }
  else if(src.id()==ID_sideeffect)
  {
    // could be done separately
    const irep_idt &statement=to_side_effect_expr(src).get_statement();
    
    if(statement==ID_nondet)
    {        
      irep_idt id="symex::nondet"+i2string(var_map.nondet_count);
      var_map.nondet_count++;
      return symbol_exprt(id, src.type());
    }
    else
      throw "instantiate_rec: unexpected side effect "+id2string(statement);
  }
  else if(src.id()==ID_dereference)
  {
    assert(false); // should be gone already
  }

  if(!src.has_operands())
    return src;

  exprt src2=src;
  
  // recursive calls on structure of 'src'
  Forall_operands(it, src2)
  {
    exprt tmp_op=instantiate_rec(*it, propagate);
    *it=tmp_op;
  }
  
  return src2;
}

/*******************************************************************\

Function: path_symex_statet::read_symbol_member_index_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::read_symbol_member_index_rec(
  const exprt &src,
  const std::string &suffix,
  const typet &type,
  bool propagate)
{
  if(src.id()==ID_symbol)
  {
    // Is this a function?
    if(src.type().id()==ID_code)
      return nil_exprt();
      
    if(src.get_bool(ID_C_SSA_symbol))
      return nil_exprt(); // SSA already
  
    irep_idt identifier=
      to_symbol_expr(src).get_identifier();

    var_mapt::var_infot &var_info=var_map(identifier, suffix, type);

    #ifdef DEBUG
    std::cout << "read_symbol_member_index_rec " << identifier
              << " var_info " << var_info.identifier << std::endl;
    #endif

    // warning: reference is not stable      
    var_statet &var_state=get_var_state(var_info);

    if(propagate && var_state.value.is_not_nil())
    {
      return var_state.value; // propagate a value
    }
    else
    {
      // we do some SSA symbol
      if(var_state.ssa_symbol.get_identifier()==irep_idt())
      {
        // produce one
        var_state.ssa_symbol.set_identifier(var_info.ssa_identifier());
        var_state.ssa_symbol.set(ID_C_SSA_symbol, true);
        var_state.ssa_symbol.type()=var_info.type;
      }
          
      return var_state.ssa_symbol;
    }
  }
  else if(src.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(src);
    
    const typet &compound_type=
      var_map.ns.follow(member_expr.struct_op().type());
    
    if(compound_type.id()==ID_struct)
    {    
      return read_symbol_member_index_rec(
        member_expr.struct_op(),
        "."+id2string(member_expr.get_component_name())+suffix,
        type,
        propagate);
    }
    else
      return nil_exprt(); // includes unions
  }
  else if(src.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(src);
    
    exprt index_tmp=read(index_expr.index(), propagate);

    // constant?    
    mp_integer i;
    if(!to_integer(index_tmp, i))
    {
      // yes
      return read_symbol_member_index_rec(
        index_expr.array(),
        "["+integer2string(i)+"]"+suffix,
        type,
        propagate);
    }
    else
    {
      // no
      return nil_exprt();
    }
  }
  else
    return nil_exprt();
}

/*******************************************************************\

Function: path_symex_statet::array_index_as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string path_symex_statet::array_index_as_string(const exprt &src) const
{
  exprt tmp=simplify_expr(src, var_map.ns);
  mp_integer i;

  if(!to_integer(tmp, i))
    return "["+integer2string(i)+"]";
  else
    return "";
}

/*******************************************************************\

Function: path_symex_statet::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::dereference_rec(
  const exprt &src,
  bool propagate)
{
  if(src.id()==ID_dereference)
  {
    const dereference_exprt &dereference_expr=to_dereference_expr(src);

    // read the address to propagate the pointers
    exprt address=read(dereference_expr.pointer(), propagate);

    // now hand over to dereferencet
    dereferencet dereference_object(var_map.ns);
    exprt address_dereferenced=dereference_object(address);
    
    // the dereferenced address is a mixture of non-SSA and SSA symbols
    // (e.g., if-guards and array indices)
    return address_dereferenced;
  }

  if(!src.has_operands())
    return src;

  exprt src2=src;
  
  {
    // recursive calls on structure of 'src'
    Forall_operands(it, src2)
    {
      exprt tmp_op=dereference_rec(*it, propagate);
      *it=tmp_op;
    }
  }
  
  return src2;
}

/*******************************************************************\

Function: path_symex_statet::instantiate_rec_address

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::instantiate_rec_address(
  const exprt &src,
  bool propagate)
{
  #ifdef DEBUG
  std::cout << "instantiate_rec_address: " << src.id() << std::endl;
  #endif

  if(src.id()==ID_symbol)
  {
    return src;
  } 
  else if(src.id()==ID_index)
  {
    assert(src.operands().size()==2);
    exprt tmp=src;
    tmp.op0()=instantiate_rec_address(src.op0(), propagate);
    tmp.op1()=instantiate_rec(src.op1(), propagate);
    return tmp;
  }
  else if(src.id()==ID_dereference)
  {
    assert(false); // should be gone already
  }
  else if(src.id()==ID_member)
  {
    assert(src.operands().size()==1);
    exprt tmp=src;
    tmp.op0()=instantiate_rec_address(src.op0(), propagate);
    return tmp;
  }
  else if(src.id()==ID_string_constant)
  {
    return src;
  }
  else if(src.id()==ID_label)
  {
    return src;
  }
  else
  {
    // this shouldn't really happen
    #ifdef DEBUG
    std::cout << "SRC: " << src.pretty() << std::endl;
    #endif
    throw "address of unexpected "+src.id_string();
  }
}

/*******************************************************************\

Function: path_symex_statet::record_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_symex_stept &path_symex_statet::record_step()
{
  // is there a context switch happening?
  if(!history.steps.empty() &&
     history.steps.back().thread_nr!=current_thread)
    no_thread_interleavings++;
  
  // add the step
  history.steps.push_back(path_symex_stept());
  path_symex_stept &step=history.steps.back();

  // copy PCs
  step.pc_vector.resize(threads.size());
  for(unsigned t=0; t<threads.size(); t++)
    step.pc_vector[t]=threads[t].pc;
  
  step.thread_nr=current_thread;
  
  return step;
}

/*******************************************************************\

Function: path_symex_statet::is_feasible

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_symex_statet::is_feasible(decision_proceduret &decision_procedure) const
{
  // feed path constraint to decision procedure
  decision_procedure << history;
  
  // check whether SAT
  switch(decision_procedure())
  {
  case decision_proceduret::D_TAUTOLOGY:
  case decision_proceduret::D_SATISFIABLE: return true;
  
  case decision_proceduret::D_UNSATISFIABLE: return false;
  
  case decision_proceduret::D_ERROR: throw "error from decsion procedure";
  }
  
  return true; // not really reachable
}
