/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_constant(const constant_exprt &expr, bvt &bv)
{
  std::size_t width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  bv.resize(width);
  
  const typet &expr_type=expr.type();
  
  if(expr_type.id()==ID_array)
  {
    std::size_t op_width=width/expr.operands().size();
    std::size_t offset=0;

    forall_operands(it, expr)
    {
      const bvt &tmp=convert_bv(*it);

      if(tmp.size()!=op_width)
        throw "convert_constant: unexpected operand width";

      for(std::size_t j=0; j<op_width; j++)
        bv[offset+j]=tmp[j];

      offset+=op_width;
    }   
    
    return;
  }
  else if(expr_type.id()==ID_range)
  {
    mp_integer from=to_range_type(expr_type).get_from();
    mp_integer value=string2integer(id2string(expr.get_value()));
    mp_integer v=value-from;
    
    std::string binary=integer2binary(v, width);

    for(std::size_t i=0; i<width; i++)
    {
      bool bit=(binary[binary.size()-i-1]=='1');
      bv[i]=const_literal(bit);
    }

    return;
  }
  else if(expr_type.id()==ID_unsignedbv ||
          expr_type.id()==ID_signedbv ||
          expr_type.id()==ID_bv ||
          expr_type.id()==ID_fixedbv ||
          expr_type.id()==ID_floatbv ||
          expr_type.id()==ID_c_enum ||
          expr_type.id()==ID_c_enum_tag ||
          expr_type.id()==ID_c_bool ||
          expr_type.id()==ID_c_bit_field ||
          expr_type.id()==ID_incomplete_c_enum)
  {
    const std::string &binary=id2string(expr.get_value());

    if(binary.size()!=width)
      throw "wrong value length in constant: "+expr.to_string();

    for(std::size_t i=0; i<width; i++)
    {
      bool bit=(binary[binary.size()-i-1]=='1');
      bv[i]=const_literal(bit);
    }

    return;
  }
  else if(expr_type.id()==ID_enumeration)
  {
    const irept::subt &elements=to_enumeration_type(expr_type).elements();
    const irep_idt &value=expr.get_value();

    for(std::size_t i=0; i<elements.size(); i++)
      if(elements[i].id()==value)
      {
        bv=bv_utils.build_constant(i, width);
        return;
      }
  }
  else if(expr_type.id()==ID_verilog_signedbv ||
          expr_type.id()==ID_verilog_unsignedbv)
  {
    const std::string &binary=id2string(expr.get_value());

    if(binary.size()*2!=width)
      throw "wrong value length in constant: "+expr.to_string();

    for(std::size_t i=0; i<binary.size(); i++)
    {
      char bit=binary[binary.size()-i-1];

      switch(bit)
      {
      case '0':
        bv[i*2]=const_literal(false);
        bv[i*2+1]=const_literal(false);
        break;
      
      case '1':
        bv[i*2]=const_literal(true);
        bv[i*2+1]=const_literal(false);
        break;
      
      case 'x':
        bv[i*2]=const_literal(false);
        bv[i*2+1]=const_literal(true);
        break;
      
      case 'z':
      case '?':
        bv[i*2]=const_literal(true);
        bv[i*2+1]=const_literal(true);
        break;
        
      default:
        throw "unknown character in Verilog constant:"+expr.to_string();
      }
    }

    return;
  }
  
  conversion_failed(expr, bv);
}
