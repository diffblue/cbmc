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

  const exprt &op=expr.op0();

  const bvt &op_bv=convert_bv(op);
  
  const typet &expr_type=ns.follow(expr.type());
  const typet &op_type=ns.follow(op.type());

  bvtypet dest_bvtype=get_bvtype(expr_type);
  bvtypet op_bvtype=get_bvtype(op_type);
  unsigned op_width=op_bv.size();

  unsigned dest_width=boolbv_width(expr_type);
  
  if(dest_width==0)
    return conversion_failed(expr, bv);
  
  bv.clear();
  bv.reserve(dest_width);

  if(op_width==0)
    return conversion_failed(expr, bv);

  switch(dest_bvtype)
  {
  case IS_RANGE:
    if(op_bvtype==IS_UNSIGNED || op_bvtype==IS_SIGNED)
    {
      mp_integer dest_from=to_range_type(expr_type).get_from();

      if(dest_from==0)
      {
        // do zero extension
        bv.resize(dest_width);
        for(unsigned i=0; i<bv.size(); i++)
          bv[i]=(i<op_bv.size()?op_bv[i]:const_literal(false));
        return;
      }
    }
    else if(op_bvtype==IS_RANGE)
    {
      mp_integer src_from=to_range_type(op_type).get_from();
      mp_integer dest_from=to_range_type(expr_type).get_from();

      if(dest_from==src_from)
      {
        // do zero extension
        bv.resize(dest_width);
        for(unsigned i=0; i<bv.size(); i++)
          bv[i]=(i<op_bv.size()?op_bv[i]:const_literal(false));
        return;
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
      
      switch(op_bvtype)
      {
      case IS_FLOAT: // float to float
        float_utils.spec=to_floatbv_type(op_type);
        bv=float_utils.conversion(op_bv, to_floatbv_type(expr_type));
        return;

      case IS_SIGNED: // signed to float
      case IS_C_ENUM:
        float_utils.spec=to_floatbv_type(expr_type);
        bv=float_utils.from_signed_integer(op_bv);
        return;

      case IS_UNSIGNED: // unsigned to float
        float_utils.spec=to_floatbv_type(expr_type);
        bv=float_utils.from_unsigned_integer(op_bv);
        return;

      case IS_BV:
        assert(op_width==dest_width);
        bv=op_bv;
        return;

      default:
        if(op_type.id()==ID_bool)
        {
          // bool to float
          
          // build a one
          ieee_floatt f;
          f.spec=to_floatbv_type(expr_type);
          f.from_integer(1);
          
          bv=convert_bv(f.to_expr());

          assert(op_width==1);
          
          Forall_literals(it, bv)
            *it=prop.land(*it, op_bv[0]);
            
          return;
        }
      }
      #endif
    }
    break;

  case IS_FIXED:
    if(op_bvtype==IS_FIXED)
    {
      // fixed to fixed
      
      unsigned dest_fraction_bits=to_fixedbv_type(expr_type).get_fraction_bits(),
               dest_int_bits=dest_width-dest_fraction_bits;
      unsigned op_fraction_bits=to_fixedbv_type(op_type).get_fraction_bits(),
               op_int_bits=op_width-op_fraction_bits;
      
      bv.resize(dest_width);
      
      // i == position after dot
      // i == 0: first position after dot

      for(unsigned i=0; i<dest_fraction_bits; i++)
      {
        // position in bv
        unsigned p=dest_fraction_bits-i-1;
      
        if(i<op_fraction_bits)
          bv[p]=op_bv[op_fraction_bits-i-1];
        else 
          bv[p]=const_literal(false); // zero padding
      }

      for(unsigned i=0; i<dest_int_bits; i++)
      {
        // position in bv
        unsigned p=dest_fraction_bits+i;
        assert(p<dest_width);
      
        if(i<op_int_bits)
          bv[p]=op_bv[i+op_fraction_bits];
        else 
          bv[p]=op_bv[op_width-1]; // sign extension
      }

      return;
    }
    else if(op_bvtype==IS_BV)
    {
      assert(op_width==dest_width);
      bv=op_bv;
      return;
    }
    else if(op_bvtype==IS_UNSIGNED ||
            op_bvtype==IS_SIGNED ||
            op_bvtype==IS_C_ENUM)
    {
      // integer to fixed

      unsigned dest_fraction_bits=
        to_fixedbv_type(expr_type).get_fraction_bits();

      for(unsigned i=0; i<dest_fraction_bits; i++)
        bv.push_back(const_literal(false)); // zero padding

      for(unsigned i=0; i<dest_width-dest_fraction_bits; i++)
      {
        literalt l;
      
        if(i<op_width)
          l=op_bv[i];
        else
        {
          if(op_bvtype==IS_SIGNED || op_bvtype==IS_C_ENUM)
            l=op_bv[op_width-1]; // sign extension
          else
            l=const_literal(false); // zero extension
        }
        
        bv.push_back(l);
      }

      return;
    }
    else if(op_type.id()==ID_bool)
    {
      // bool to fixed
      unsigned fraction_bits=
        to_fixedbv_type(expr_type).get_fraction_bits();

      assert(op_width==1);

      for(unsigned i=0; i<dest_width; i++)
      {
        if(i==fraction_bits)
          bv.push_back(op_bv[0]);
        else
          bv.push_back(const_literal(false));
      }

      return;
    }
    break;
  
  case IS_UNSIGNED:
  case IS_SIGNED:
  case IS_C_ENUM:
    switch(op_bvtype)
    {
    case IS_FLOAT: // float to integer
      {
        #ifdef HAVE_FLOATBV
        // note that float to int conversion in ANSI-C is hardwired
        // to ROUND TO ZERO, also known as truncate.
        float_utilst float_utils(prop);
        float_utils.rounding_mode=ieee_floatt::ROUND_TO_ZERO;
        float_utils.spec=to_floatbv_type(op_type);
        bv=float_utils.to_integer(op_bv, dest_width, dest_bvtype!=IS_UNSIGNED);
        return;
        #else
        return conversion_failed(expr, bv);
        #endif
      }
     
    case IS_FIXED: // fixed to integer
      {
        unsigned op_fraction_bits=
          to_fixedbv_type(op_type).get_fraction_bits();

        for(unsigned i=0; i<dest_width; i++)
        {
          if(i<op_width-op_fraction_bits)
            bv.push_back(op_bv[i+op_fraction_bits]);
          else
          {
            if(dest_bvtype==IS_SIGNED)
              bv.push_back(op_bv[op_width-1]); // sign extension
            else
              bv.push_back(const_literal(false)); // zero extension
          }
        }
        
        // we might need to round up in case of negative numbers
        // e.g., (int)(-1.00001)==1
        
        bvt fraction_bits_bv=op_bv;
        fraction_bits_bv.resize(op_fraction_bits);
        literalt round_up=
          prop.land(prop.lor(fraction_bits_bv), op_bv.back());

        bv=bv_utils.incrementer(bv, round_up);

        return;
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
          op_bvtype==IS_SIGNED || op_bvtype==IS_C_ENUM;

        for(unsigned i=0; i<dest_width; i++)
        {
          if(i<op_width)
            bv.push_back(op_bv[i]);
          else if(sign_extension)
            bv.push_back(op_bv[op_width-1]); // sign extension
          else
            bv.push_back(const_literal(false));
        }

        return;
      }
      
    default:
      if(op_type.id()==ID_bool)
      {
        // bool to integer

        assert(op_width==1);

        for(unsigned i=0; i<dest_width; i++)
        {
          if(i==0)
            bv.push_back(op_bv[0]);
          else
            bv.push_back(const_literal(false));
        }

        return;
      }
    }
    break;
    
  case IS_VERILOGBV:
    if(op_bvtype==IS_UNSIGNED)
    {
      for(unsigned i=0, j=0; i<dest_width; i+=2, j++)
      {
        if(j<op_width)
          bv.push_back(op_bv[j]);
        else
          bv.push_back(const_literal(false));

        bv.push_back(const_literal(false));
      }

      return;
    }
    break;

  case IS_BV:
    assert(op_width==dest_width);
    bv=op_bv;
    return;
    
  default:
    if(expr_type.id()==ID_array)
    {
      if(op_width==dest_width)
      {
        bv=op_bv;
        return;
      }
    }
    else if(expr_type.id()==ID_struct)
    {
      const struct_typet &dest_struct =
        to_struct_type(expr_type);

      if(op_type.id()==ID_struct)
      {
        // we do subsets

        bv.resize(dest_width, const_literal(false));

        const struct_typet &op_struct =
          to_struct_type(expr.op0().type());

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
              bv[offset+j]=prop.new_variable();
          }
          else
          {
            // found
            if(dest_comp[i].type()!=dest_comp[it->second].type())
            {
              // filling with free variables
              for(unsigned j=0; j<comp_width; j++)
                bv[offset+j]=prop.new_variable();
            }
            else
            {
              unsigned op_offset=op_offsets[it->second];
              for(unsigned j=0; j<comp_width; j++)
                bv[offset+j]=op_bv[op_offset+j];
            }
          }
        }

        return;
      }
    }

  }

  conversion_failed(expr, bv);
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
