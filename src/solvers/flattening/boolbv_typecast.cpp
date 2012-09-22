/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <std_types.h>

#include "boolbv.h"
#include "boolbv_type.h"

#ifdef HAVE_FLOATBV
#include "../floatbv/float_utils.h"
#endif

/*******************************************************************\

Function: boolbvt::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_typecast(const exprt &expr, bvt &bv)
{
  if(expr.operands().size()!=1)
    throw "typecast takes one operand";

  const typet &expr_type=ns.follow(expr.type());
  const exprt &op=expr.op0();
  const typet &op_type=ns.follow(op.type());
  const bvt &op_bv=convert_bv(op);  

  if(type_conversion(op_type, op_bv, expr_type, bv))
    return conversion_failed(expr, bv);
}

/*******************************************************************\

Function: boolbvt::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool boolbvt::type_conversion(
  const typet &src_type, const bvt &src,
  const typet &dest_type, bvt &dest)
{
  bvtypet dest_bvtype=get_bvtype(dest_type);
  bvtypet src_bvtype=get_bvtype(src_type);
  unsigned src_width=src.size();

  unsigned dest_width=boolbv_width(dest_type);
  
  if(dest_width==0 || src_width==0)
    return true;
  
  dest.clear();
  dest.reserve(dest_width);

  if(dest_type.id()==ID_complex)
  {
    if(src_type==dest_type.subtype())
    {
      forall_literals(it, src)
      dest.push_back(*it);

      // pad with zeros
      for(unsigned i=src.size(); i<dest_width; i++)
        dest.push_back(const_literal(false));

      return false;
    }
    else if(src_type.id()==ID_complex)
    {
      // recursively do both halfs
      bvt lower, upper, lower_res, upper_res;
      lower.assign(src.begin(), src.begin()+src.size()/2);
      upper.assign(src.begin()+src.size()/2, src.end());
      type_conversion(ns.follow(src_type.subtype()), lower, ns.follow(dest_type.subtype()), lower_res);
      type_conversion(ns.follow(src_type.subtype()), upper, ns.follow(dest_type.subtype()), upper_res);
      assert(lower_res.size()+upper_res.size()==dest_width);
      dest=lower_res;
      dest.insert(dest.end(), upper_res.begin(), upper_res.end());
      return false;
    }
  }
  
  if(src_type.id()==ID_complex)
  {
    assert(dest_type.id()!=ID_complex);
    if(dest_type.id()==ID_signedbv ||
       dest_type.id()==ID_unsignedbv ||
       dest_type.id()==ID_floatbv ||
       dest_type.id()==ID_fixedbv ||
       dest_type.id()==ID_c_enum ||
       dest_type.id()==ID_bool)
    {
      // A cast from complex x to real T
      // is (T) __real__ x.
      bvt tmp_src(src);
      tmp_src.resize(src.size()/2); // cut off imag part
      return type_conversion(src_type.subtype(), tmp_src, dest_type, dest);
    }
  }
  
  switch(dest_bvtype)
  {
  case IS_RANGE:
    if(src_bvtype==IS_UNSIGNED || src_bvtype==IS_SIGNED)
    {
      mp_integer dest_from=to_range_type(dest_type).get_from();

      if(dest_from==0)
      {
        // do zero extension
        dest.resize(dest_width);
        for(unsigned i=0; i<dest.size(); i++)
          dest[i]=(i<src.size()?src[i]:const_literal(false));

        return false;
      }
    }
    else if(src_bvtype==IS_RANGE)
    {
      mp_integer src_from=to_range_type(src_type).get_from();
      mp_integer dest_from=to_range_type(dest_type).get_from();

      if(dest_from==src_from)
      {
        // do zero extension
        dest.resize(dest_width);
        for(unsigned i=0; i<dest.size(); i++)
          dest[i]=(i<src.size()?src[i]:const_literal(false));

        return false;
      }
      else
      {
        // need to do arithmetic
      }
    }
    break;
    
  case IS_FLOAT: // to float
    {
      #ifdef HAVE_FLOATBV
      float_utilst float_utils(prop);
      
      switch(src_bvtype)
      {
      case IS_FLOAT: // float to float
        float_utils.spec=to_floatbv_type(src_type);
        dest=float_utils.conversion(src, to_floatbv_type(dest_type));
        return false;

      case IS_SIGNED: // signed to float
      case IS_C_ENUM:
        float_utils.spec=to_floatbv_type(dest_type);
        dest=float_utils.from_signed_integer(src);
        return false;

      case IS_UNSIGNED: // unsigned to float
        float_utils.spec=to_floatbv_type(dest_type);
        dest=float_utils.from_unsigned_integer(src);
        return false;

      case IS_BV:
        assert(src_width==dest_width);
        dest=src;
        return false;

      default:
        if(src_type.id()==ID_bool)
        {
          // bool to float
          
          // build a one
          ieee_floatt f;
          f.spec=to_floatbv_type(dest_type);
          f.from_integer(1);
          
          dest=convert_bv(f.to_expr());

          assert(src_width==1);
          
          Forall_literals(it, dest)
            *it=prop.land(*it, src[0]);
            
          return false;
        }
      }
      #endif
    }
    break;

  case IS_FIXED:
    if(src_bvtype==IS_FIXED)
    {
      // fixed to fixed
      
      unsigned dest_fraction_bits=to_fixedbv_type(dest_type).get_fraction_bits(),
               dest_int_bits=dest_width-dest_fraction_bits;
      unsigned op_fraction_bits=to_fixedbv_type(src_type).get_fraction_bits(),
               op_int_bits=src_width-op_fraction_bits;
      
      dest.resize(dest_width);
      
      // i == position after dot
      // i == 0: first position after dot

      for(unsigned i=0; i<dest_fraction_bits; i++)
      {
        // position in bv
        unsigned p=dest_fraction_bits-i-1;
      
        if(i<op_fraction_bits)
          dest[p]=src[op_fraction_bits-i-1];
        else 
          dest[p]=const_literal(false); // zero padding
      }

      for(unsigned i=0; i<dest_int_bits; i++)
      {
        // position in bv
        unsigned p=dest_fraction_bits+i;
        assert(p<dest_width);
      
        if(i<op_int_bits)
          dest[p]=src[i+op_fraction_bits];
        else 
          dest[p]=src[src_width-1]; // sign extension
      }

      return false;
    }
    else if(src_bvtype==IS_BV)
    {
      assert(src_width==dest_width);
      dest=src;
      return false;
    }
    else if(src_bvtype==IS_UNSIGNED ||
            src_bvtype==IS_SIGNED ||
            src_bvtype==IS_C_ENUM)
    {
      // integer to fixed

      unsigned dest_fraction_bits=
        to_fixedbv_type(dest_type).get_fraction_bits();

      for(unsigned i=0; i<dest_fraction_bits; i++)
        dest.push_back(const_literal(false)); // zero padding

      for(unsigned i=0; i<dest_width-dest_fraction_bits; i++)
      {
        literalt l;
      
        if(i<src_width)
          l=src[i];
        else
        {
          if(src_bvtype==IS_SIGNED || src_bvtype==IS_C_ENUM)
            l=src[src_width-1]; // sign extension
          else
            l=const_literal(false); // zero extension
        }
        
        dest.push_back(l);
      }

      return false;
    }
    else if(src_type.id()==ID_bool)
    {
      // bool to fixed
      unsigned fraction_bits=
        to_fixedbv_type(dest_type).get_fraction_bits();

      assert(src_width==1);

      for(unsigned i=0; i<dest_width; i++)
      {
        if(i==fraction_bits)
          dest.push_back(src[0]);
        else
          dest.push_back(const_literal(false));
      }

      return false;
    }
    break;
  
  case IS_UNSIGNED:
  case IS_SIGNED:
  case IS_C_ENUM:
    switch(src_bvtype)
    {
    case IS_FLOAT: // float to integer
      {
        #ifdef HAVE_FLOATBV
        // note that float to int conversion in ANSI-C is hardwired
        // to ROUND TO ZERO, also known as truncate.
        float_utilst float_utils(prop);
        float_utils.rounding_mode=ieee_floatt::ROUND_TO_ZERO;
        float_utils.spec=to_floatbv_type(src_type);
        dest=float_utils.to_integer(src, dest_width, dest_bvtype!=IS_UNSIGNED);
        return false;
        #else
        return true;
        #endif
      }
     
    case IS_FIXED: // fixed to integer
      {
        unsigned op_fraction_bits=
          to_fixedbv_type(src_type).get_fraction_bits();

        for(unsigned i=0; i<dest_width; i++)
        {
          if(i<src_width-op_fraction_bits)
            dest.push_back(src[i+op_fraction_bits]);
          else
          {
            if(dest_bvtype==IS_SIGNED)
              dest.push_back(src[src_width-1]); // sign extension
            else
              dest.push_back(const_literal(false)); // zero extension
          }
        }
        
        // we might need to round up in case of negative numbers
        // e.g., (int)(-1.00001)==1
        
        bvt fraction_bits_bv=src;
        fraction_bits_bv.resize(op_fraction_bits);
        literalt round_up=
          prop.land(prop.lor(fraction_bits_bv), src.back());

        dest=bv_utils.incrementer(dest, round_up);

        return false;
      }

    case IS_UNSIGNED: // integer to integer
    case IS_SIGNED:
    case IS_C_ENUM:
      {
        // We do sign extension for any source type
        // that is signed, independently of the
        // destination type.
        // E.g., ((short)(ulong)(short)-1)==-1
        bool sign_extension=
          src_bvtype==IS_SIGNED || src_bvtype==IS_C_ENUM;

        for(unsigned i=0; i<dest_width; i++)
        {
          if(i<src_width)
            dest.push_back(src[i]);
          else if(sign_extension)
            dest.push_back(src[src_width-1]); // sign extension
          else
            dest.push_back(const_literal(false));
        }

        return false;
      }
      
    default:
      if(src_type.id()==ID_bool)
      {
        // bool to integer

        assert(src_width==1);

        for(unsigned i=0; i<dest_width; i++)
        {
          if(i==0)
            dest.push_back(src[0]);
          else
            dest.push_back(const_literal(false));
        }

        return false;
      }
    }
    break;
    
  case IS_VERILOGBV:
    if(src_bvtype==IS_UNSIGNED)
    {
      for(unsigned i=0, j=0; i<dest_width; i+=2, j++)
      {
        if(j<src_width)
          dest.push_back(src[j]);
        else
          dest.push_back(const_literal(false));

        dest.push_back(const_literal(false));
      }

      return false;
    }
    break;

  case IS_BV:
    assert(src_width==dest_width);
    dest=src;
    return false;
    
  default:
    if(dest_type.id()==ID_array)
    {
      if(src_width==dest_width)
      {
        dest=src;
        return false;
      }
    }
    else if(dest_type.id()==ID_struct)
    {
      const struct_typet &dest_struct =
        to_struct_type(dest_type);

      if(src_type.id()==ID_struct)
      {
        // we do subsets

        dest.resize(dest_width, const_literal(false));

        const struct_typet &op_struct =
          to_struct_type(src_type);

        const struct_typet::componentst &dest_comp=
          dest_struct.components();

        const struct_typet::componentst &op_comp=
          op_struct.components();

        // build offset maps
        offset_mapt op_offsets, dest_offsets;

        build_offset_map(op_struct, op_offsets);
        build_offset_map(dest_struct, dest_offsets);

        // build name map
        typedef std::map<irep_idt, unsigned> op_mapt;
        op_mapt op_map;

        for(unsigned i=0; i<op_comp.size(); i++)
          op_map[op_comp[i].get_name()]=i;

        // now gather required fields
        for(unsigned i=0;
            i<dest_comp.size();
            i++)
        {
          unsigned offset=dest_offsets[i];
          unsigned int comp_width=boolbv_width(dest_comp[i].type());
          if(comp_width==0) continue;

          op_mapt::const_iterator it=
            op_map.find(dest_comp[i].get_name());

          if(it==op_map.end())
          {
            // not found

            // filling with free variables
            for(unsigned j=0; j<comp_width; j++)
              dest[offset+j]=prop.new_variable();
          }
          else
          {
            // found
            if(dest_comp[i].type()!=dest_comp[it->second].type())
            {
              // filling with free variables
              for(unsigned j=0; j<comp_width; j++)
                dest[offset+j]=prop.new_variable();
            }
            else
            {
              unsigned op_offset=op_offsets[it->second];
              for(unsigned j=0; j<comp_width; j++)
                dest[offset+j]=src[op_offset+j];
            }
          }
        }

        return false;
      }
    }

  }

  return true;
}

/*******************************************************************\

Function: boolbvt::convert_typecast

  Inputs:

 Outputs:

 Purpose: conversion from bitvector types to boolean

\*******************************************************************/

literalt boolbvt::convert_typecast(const exprt &expr)
{
  if(expr.operands().size()==1)
  {
    if(expr.op0().type().id()==ID_range)
    {
      mp_integer from=string2integer(expr.op0().type().get_string(ID_from));
      mp_integer to=string2integer(expr.op0().type().get_string(ID_to));

      if(from==1 && to==1)
        return const_literal(true);
      else if(from==0 && to==0)
        return const_literal(false);
    }

    const bvt &bv=convert_bv(expr.op0());
    
    if(bv.size()!=0)
      return prop.lor(bv);
  }
  
  return SUB::convert_rest(expr);
}
