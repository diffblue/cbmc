/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/simplify_expr.h>
#include <util/arith_tools.h>
#include <util/i2string.h>

#include <pointer-analysis/dereference.h>

#include <goto-symex/adjust_float_expressions.h>
#include <goto-symex/rewrite_union.h>

#include "path_symex_state.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

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
  
  // This has five phases!
  // 1. Floating-point expression adjustment (rounding mode)
  // 2. Rewrite unions into byte operators
  // 3. Dereferencing, including propagation of pointers.
  // 4. Rewriting to SSA symbols
  // 5. Simplifier
  
  exprt tmp1=src;
  adjust_float_expressions(tmp1, var_map.ns);
  
  exprt tmp2=tmp1;
  rewrite_union(tmp2, var_map.ns);

  // we force propagation for dereferencing
  exprt tmp3=dereference_rec(tmp2, true);
  
  exprt tmp4=instantiate_rec(tmp3, propagate);
  
  exprt tmp5=simplify_expr(tmp4, var_map.ns);

  #ifdef DEBUG
  //std::cout << " ==> " << tmp.pretty() << std::endl;
  #endif

  return tmp5;
}

/*******************************************************************\

Function: path_symex_statet::expand_structs_and_arrays

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::expand_structs_and_arrays(const exprt &src)
{
  #ifdef DEBUG
  std::cout << "expand_structs_and_arrays: "
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
      result.operands()[i]=expand_structs_and_arrays(new_src);
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
        result.operands()[i]=expand_structs_and_arrays(new_src);
      }
      
      return result; // done
    }
    else
    {
      // TODO: variable-sized array
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
      operands[i]=expand_structs_and_arrays(new_src);
    }

    return result; // done
  }
  
  return src;
}

/*******************************************************************\

Function: path_symex_statet::array_theory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::array_theory(const exprt &src, bool propagate)
{
  // top-level constant-sized arrays only right now
  
  if(src.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(src);
    exprt index_tmp1=read(index_expr.index(), propagate);    
    exprt index_tmp2=simplify_expr(index_tmp1, var_map.ns);

    if(!index_tmp2.is_constant())
    {
      const array_typet &array_type=to_array_type(index_expr.array().type());
      const typet &subtype=array_type.subtype();
      
      if(array_type.size().is_constant())
      {
        mp_integer size;
        if(to_integer(array_type.size(), size))
          throw "failed to convert array size";
          
        unsigned long long size_int=integer2unsigned(size);
        
        exprt result=nil_exprt();
        
        // split it up
        for(unsigned long long i=0; i<size_int; ++i)
        {
          exprt index=from_integer(i, index_expr.index().type());
          exprt new_src=index_exprt(index_expr.array(), index, subtype);

          if(result.is_nil())
            result=new_src;
          else
          {
            equal_exprt index_equal(index_expr.index(), index);
            result=if_exprt(index_equal, new_src, result);
          }
        }
        
        return result; // done
      }
      else
      {
        // TODO: variable-sized array
      }
      
    }
  }

  return src;
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
  
  if(is_symbol_member_index(src))  
  {
    exprt tmp_symbol_member_index=
      read_symbol_member_index(src, propagate);
  
    assert(tmp_symbol_member_index.is_not_nil());
    return tmp_symbol_member_index; // yes!
  }
  
  if(src.id()==ID_address_of)
  {
    assert(src.operands().size()==1);
    exprt tmp=src;
    tmp.op0()=instantiate_rec_address(tmp.op0(), propagate);
    return tmp;
  }
  else if(src.id()==ID_side_effect)
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
  else if(src.id()==ID_member)
  {
    const typet &compound_type=
      var_map.ns.follow(to_member_expr(src).struct_op().type());
      
    if(compound_type.id()==ID_struct)
    {  
      // do nothing
    }
    else if(compound_type.id()==ID_union)
    {
      // should already have been rewritten to byte_extract
      throw "unexpected union member";
    }
    else
    {
      throw "member expects struct or union type"+src.pretty();
    }
  }
  else if(src.id()==ID_byte_extract_little_endian ||
          src.id()==ID_byte_extract_big_endian)
  {
  }
  else if(src.id()==ID_symbol)
  {
    // must be SSA already, or code
    assert(src.type().id()==ID_code ||
           src.get_bool(ID_C_SSA_symbol));
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
  const typet &src_type=var_map.ns.follow(src.type());

  // don't touch function symbols
  if(src_type.id()==ID_code)
    return nil_exprt();

  // is this a struct/array/vector that needs to be expanded?
  exprt final=expand_structs_and_arrays(src);
  
  if(final.id()==ID_struct ||
     final.id()==ID_array ||
     final.id()==ID_vector)
  {
    Forall_operands(it, final)
      *it=read_symbol_member_index(*it, propagate); // rec. call
    return final;
  }
  
  // now do array theory
  final=array_theory(final, propagate);
  
  if(final.id()==ID_if)
  {
    assert(final.operands().size()==3);
    final.op0()=instantiate_rec(final.op0(), propagate); // rec. call
    final.op1()=read_symbol_member_index(final.op1(), propagate); // rec. call
    final.op2()=read_symbol_member_index(final.op2(), propagate); // rec. call
    return final;
  }

  std::string suffix="";
  exprt current=src;
  
  // the loop avoids recursion
  while(current.id()!=ID_symbol)
  {
    exprt next=nil_exprt();
  
    if(current.id()==ID_member)
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
      
      std::string index_string=array_index_as_string(index_tmp);
      
      // go into next iteration
      next=index_expr.array();
      suffix=index_string+suffix;
    }
    else
      return nil_exprt();

    // next round  
    assert(next.is_not_nil());
    current=next;
  }

  assert(current.id()==ID_symbol);
  
  if(current.get_bool(ID_C_SSA_symbol))
    return nil_exprt(); // SSA already

  irep_idt identifier=
    to_symbol_expr(current).get_identifier();

  var_mapt::var_infot &var_info=
    var_map(identifier, suffix, src.type());

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

/*******************************************************************\

Function: path_symex_statet::is_symbol_member_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_symex_statet::is_symbol_member_index(const exprt &src) const
{
  const typet final_type=src.type();
  
  // don't touch function symbols
  if(var_map.ns.follow(final_type).id()==ID_code)
    return false;

  const exprt *current=&src;

  // the loop avoids recursion
  while(true)
  {
    const exprt *next=0;
  
    if(current->id()==ID_symbol)
    {
      if(current->get_bool(ID_C_SSA_symbol))
        return false; // SSA already

      return true;    
    }
    else if(current->id()==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(*current);
      
      const typet &compound_type=
        var_map.ns.follow(member_expr.struct_op().type());
      
      if(compound_type.id()==ID_struct)
      { 
        // go into next iteration
        next=&(member_expr.struct_op());
      }
      else
        return false; // includes unions, deliberatley
    }
    else if(current->id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(*current);
      
      // go into next iteration
      next=&(index_expr.array());
    }
    else
      return false;

    // next round  
    assert(next!=0);
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
    throw "address of unexpected `"+src.id_string()+"'";
  }
}

