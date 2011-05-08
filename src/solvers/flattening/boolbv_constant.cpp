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

void boolbvt::convert_constant(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  bv.resize(width);
  
  if(expr.type().id()==ID_array)
  {
    unsigned op_width=width/expr.operands().size();
    unsigned offset=0;

    forall_operands(it, expr)
    {
      bvt tmp;

      convert_bv(*it, tmp);

      if(tmp.size()!=op_width)
        throw "convert_constant: unexpected operand width";

      for(unsigned j=0; j<op_width; j++)
        bv[offset+j]=tmp[j];

      offset+=op_width;
    }   
    
    return;
  }
  else if(expr.type().id()==ID_range)
  {
    mp_integer from=string2integer(expr.type().get_string(ID_from));
    mp_integer value=string2integer(expr.get_string(ID_value));
    mp_integer v=value-from;
    
    std::string binary=integer2binary(v, width);

    for(unsigned i=0; i<width; i++)
    {
      bool bit=(binary[binary.size()-i-1]=='1');
      bv[i]=const_literal(bit);
    }

    return;
  }
  else if(expr.type().id()==ID_c_enum ||
          expr.type().id()==ID_incomplete_c_enum)
  {
    mp_integer value=string2integer(expr.get_string(ID_value));
    std::string binary=integer2binary(value, width);
    assert(width!=0);

    for(unsigned i=0; i<width; i++)
    {
      bool bit=(binary[binary.size()-i-1]=='1');
      bv[i]=const_literal(bit);
    }

    return;
  }
  else if(expr.type().id()==ID_unsignedbv ||
          expr.type().id()==ID_signedbv ||
          expr.type().id()==ID_bv ||
          expr.type().id()==ID_fixedbv ||
          expr.type().id()==ID_floatbv)
  {
    const std::string &binary=expr.get_string(ID_value);

    if(binary.size()!=width)
      throw "wrong value length in constant: "+expr.to_string();

    for(unsigned i=0; i<width; i++)
    {
      bool bit=(binary[binary.size()-i-1]=='1');
      bv[i]=const_literal(bit);
    }

    return;
  }
  else if(expr.type().id()==ID_verilogbv)
  {
    const std::string &binary=expr.get_string(ID_value);

    if(binary.size()*2!=width)
      throw "wrong value length in constant: "+expr.to_string();

    for(unsigned i=0; i<binary.size(); i++)
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
