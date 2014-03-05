/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com
        Alex Horn, alex.horn@cs.ox.ac.uk

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
  const locst &locs,
  path_symex_historyt &path_symex_history)
{
  return path_symex_statet(
    var_map,
    locs,
    path_symex_step_reft(path_symex_history),
    path_symex_statet::branchest());
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
  
  // This has four phases!
  // 1. Floating-point expression adjustment (rounding mode)
  // 2. Dereferencing, including propagation of pointers.
  // 3. Rewriting to SSA symbols
  // 4. Simplifier
  
  exprt tmp1=src;
  adjust_float_expressions(tmp1, var_map.ns);

  // we force propagation for dereferencing
  exprt tmp2=dereference_rec(tmp1, true);
  
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

  const typet &src_type=var_map.ns.follow(src.type());
  
  if(src_type.id()==ID_struct) // src is a struct
  {
    const struct_typet &struct_type=to_struct_type(src_type);
    const struct_typet::componentst &components=struct_type.components();
    
    struct_exprt result(src.type());
    result.operands().resize(components.size());

    // split it up into components
    for(unsigned i=0; i<components.size(); i++)
    {
      const typet &subtype=components[i].type();
      const irep_idt &component_name=components[i].get_name();

      exprt new_src;
      if(src.id()==ID_struct) // struct constructor?
      {
        assert(src.operands().size()==components.size());
        new_src=src.operands()[i];
      }
      else
        new_src=member_exprt(src, component_name, subtype);
      
      // recursive call
      result.operands()[i]=instantiate_rec(new_src, propagate);
    }

    return result; // done
  } 
  else if(src_type.id()==ID_array) // src is an array
  {
    const array_typet &array_type=to_array_type(src_type);
    const typet &subtype=array_type.subtype();
    
    if(array_type.size().is_constant())
    {
      mp_integer size;
      if(to_integer(array_type.size(), size))
        throw "failed to convert array size";
        
      unsigned long long size_int=integer2unsigned(size);
        
      array_exprt result(array_type);
      result.operands().resize(size_int);
    
      // split it up into elements
      for(unsigned long long i=0; i<size_int; ++i)
      {
        exprt index=from_integer(i, array_type.size().type());
        exprt new_src=index_exprt(src, index, subtype);
        
        // array constructor?
        if(src.id()==ID_array)
          new_src=simplify_expr(new_src, var_map.ns);
        
        // recursive call
        result.operands()[i]=instantiate_rec(new_src, propagate);
      }
      
      return result; // done
    }
    else
    {
      // TODO
    }
  }
  else if(src_type.id()==ID_vector) // src is a vector
  {
    const vector_typet &vector_type=to_vector_type(src_type);
    const typet &subtype=vector_type.subtype();
    
    if(!vector_type.size().is_constant())
      throw "vector with non-constant size";

    mp_integer size;
    if(to_integer(vector_type.size(), size))
      throw "failed to convert vector size";
      
    unsigned long long int size_int=integer2unsigned(size);
    
    vector_exprt result(vector_type);
    exprt::operandst &operands=result.operands();
    operands.resize(size_int);
  
    // split it up into elements
    for(unsigned long long i=0; i<size_int; ++i)
    {
      exprt index=from_integer(i, vector_type.size().type());
      exprt new_src=index_exprt(src, index, subtype);
      
      // vector constructor?
      if(src.id()==ID_vector)
        new_src=simplify_expr(new_src, var_map.ns);
      
      // recursive call
      operands[i]=instantiate_rec(new_src, propagate);
    }

    return result; // done
  }

  // check whether this is a symbol(.member|[index])*
  
  {
    exprt tmp_symbol_member_index=
      read_symbol_member_index(src, propagate);
  
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
    // dereferencet has run already, so we should only be left with
    // integer addresses. Will transform into __CPROVER_memory[]
    // eventually.
  }
  else if(src.id()==ID_index)
  {
    // avoids indefinite recursion above
    return src;
  }
  else if(src.id()==ID_member)
  {
    const typet &compound_type=
      var_map.ns.follow(to_member_expr(src).struct_op().type());
      
    if(compound_type.id()==ID_struct)
    {  
      // avoids indefinite recursion above
      return src;
    }
    else if(compound_type.id()==ID_union)
    {
      member_exprt tmp=to_member_expr(src);
      tmp.struct_op()=instantiate_rec(tmp.struct_op(), propagate);
      return tmp;
    }
    else
    {
      throw "member expects struct or union type"+src.pretty();
    }
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

Function: path_symex_statet::read_symbol_member_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::read_symbol_member_index(
  const exprt &src,
  bool propagate)
{
  std::string suffix="";
  exprt current=src;
  const typet final_type=src.type();
  exprt::operandst indices;
  
  // don't touch function symbols
  if(var_map.ns.follow(final_type).id()==ID_code)
    return nil_exprt();

  // the loop avoids recursion
  while(true)
  {
    exprt next=nil_exprt();
  
    if(current.id()==ID_symbol)
    {
      if(current.get_bool(ID_C_SSA_symbol))
        return nil_exprt(); // SSA already
    
      irep_idt identifier=
        to_symbol_expr(current).get_identifier();

      var_mapt::var_infot &var_info=
        var_map(identifier, suffix, final_type);

      #ifdef DEBUG
      std::cout << "read_symbol_member_index_rec " << identifier
                << " var_info " << var_info.full_identifier << std::endl;
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
          var_state.ssa_symbol=var_info.ssa_symbol();
        }
            
        return var_state.ssa_symbol;
      }
    }
    else if(current.id()==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(current);
      
      const typet &compound_type=
        var_map.ns.follow(member_expr.struct_op().type());
      
      if(compound_type.id()==ID_struct)
      { 
        // go into next iteration
        next=member_expr.struct_op();
        suffix="."+id2string(member_expr.get_component_name())+suffix;
      }
      else
        return nil_exprt(); // includes unions, deliberatley
    }
    else if(current.id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(current);
      
      exprt index_tmp=read(index_expr.index(), propagate);
      indices.push_back(index_tmp);
      
      std::string index_string=array_index_as_string(index_tmp);
      
      // go into next iteration
      next=index_expr.array();
      suffix=index_string+suffix;
    }
    else
    {
      return nil_exprt();
    }

    // next round  
    assert(next.is_not_nil());
    current=next;
  }
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
    return "[*]";
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

    // now hand over to dereference
    exprt address_dereferenced=::dereference(address, var_map.ns);
    
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
    // dereferenct ran before, and this can only be *(type *)integer-address,
    // which we simply instantiate as non-address
    dereference_exprt tmp=to_dereference_expr(src);
    tmp.pointer()=instantiate_rec(tmp.pointer(), propagate);
    return tmp;
  }
  else if(src.id()==ID_member)
  {
    member_exprt tmp=to_member_expr(src);
    tmp.struct_op()=instantiate_rec_address(tmp.struct_op(), propagate);
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
  else if(src.id()==ID_byte_extract_big_endian ||
          src.id()==ID_byte_extract_little_endian)
  {
    assert(src.operands().size()==2);
    exprt tmp=src;
    tmp.op0()=instantiate_rec_address(src.op0(), propagate);
    tmp.op1()=instantiate_rec(src.op1(), propagate);
    return tmp;
  }
  else if(src.id()==ID_if)
  {
    if_exprt if_expr=to_if_expr(src);
    if_expr.true_case()=instantiate_rec_address(if_expr.true_case(), propagate);
    if_expr.false_case()=instantiate_rec_address(if_expr.false_case(), propagate);
    if_expr.cond()=instantiate_rec(if_expr.cond(), propagate);
    return if_expr;
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

void path_symex_statet::record_step()
{
  // is there a context switch happening?
  if(!history.is_nil() &&
     history->thread_nr!=current_thread)
    no_thread_interleavings++;
    
  // update our statistics
  depth++;

  // add the step
  history.generate_successor();
  path_symex_stept &step=*history;

  // copy PC
  assert(current_thread<threads.size());
  step.pc=threads[current_thread].pc;
  step.thread_nr=current_thread;
}

/*******************************************************************\

Function: path_symex_statet::record_branch_step

  Inputs: whether branch was taken, or not

 Outputs:

 Purpose: like record_step() and record branch decision

\*******************************************************************/

void path_symex_statet::record_branch_step(bool taken)
{
  assert(get_instruction()->is_goto());

#ifdef PATH_SYMEX_LAZY_BRANCH
  if(!branches.empty() || history.is_nil())
#endif
  {
    // get_branches() relies on branch decisions
    branches.push_back(taken);

    if(get_instruction()->is_goto())
    {
      branches_restore++;
    }
    else
    {
      assert(pc()==locs.entry_loc);
      assert(history.is_nil());
    }
  }

  record_step();
}

/*******************************************************************\

Function: path_symex_statet::is_feasible

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_symex_statet::is_feasible(
  decision_proceduret &decision_procedure) const
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

/*******************************************************************\

Function: path_symex_statet::check_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_symex_statet::check_assertion(
  decision_proceduret &decision_procedure)
{
  const goto_programt::instructiont &instruction=*get_instruction();

  // assert that this is an assertion
  assert(instruction.is_assert());

  // the assertion in SSA
  exprt assertion=read(instruction.guard);
  
  // trivial?
  if(assertion.is_true()) return true; // no error

  // the path constraint
  decision_procedure << history;

  // negate the assertion
  decision_procedure.set_to(assertion, false);

  // check whether SAT  
  switch(decision_procedure.dec_solve())
  {
  case decision_proceduret::D_TAUTOLOGY:
  case decision_proceduret::D_SATISFIABLE:
    return false; // error
   
  case decision_proceduret::D_UNSATISFIABLE:
    return true; // no error
  
  default:
    throw "error from decision procedure";
  }

  return true; // not really reachable
}

