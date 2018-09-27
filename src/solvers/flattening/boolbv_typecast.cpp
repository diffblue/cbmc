/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <cassert>

#include <util/std_types.h>

#include <solvers/floatbv/float_utils.h>

#include "boolbv_type.h"
#include "c_bit_field_replacement_type.h"

bvt boolbvt::convert_bv_typecast(const typecast_exprt &expr)
{
  const typet &expr_type=ns.follow(expr.type());
  const exprt &op=expr.op();
  const typet &op_type=ns.follow(op.type());
  const bvt &op_bv=convert_bv(op);

  bvt bv;

  if(type_conversion(op_type, op_bv, expr_type, bv))
    return conversion_failed(expr);

  return bv;
}

bool boolbvt::type_conversion(
  const typet &src_type, const bvt &src,
  const typet &dest_type, bvt &dest)
{
  bvtypet dest_bvtype=get_bvtype(dest_type);
  bvtypet src_bvtype=get_bvtype(src_type);

  if(src_bvtype==bvtypet::IS_C_BIT_FIELD)
    return
      type_conversion(
        c_bit_field_replacement_type(to_c_bit_field_type(src_type), ns),
        src,
        dest_type,
        dest);

  if(dest_bvtype==bvtypet::IS_C_BIT_FIELD)
    return
      type_conversion(
        src_type,
        src,
        c_bit_field_replacement_type(to_c_bit_field_type(dest_type), ns),
        dest);

  std::size_t src_width=src.size();
  std::size_t dest_width=boolbv_width(dest_type);

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
      for(std::size_t i=src.size(); i<dest_width; i++)
        dest.push_back(const_literal(false));

      return false;
    }
    else if(src_type.id()==ID_complex)
    {
      // recursively do both halfs
      bvt lower, upper, lower_res, upper_res;
      lower.assign(src.begin(), src.begin()+src.size()/2);
      upper.assign(src.begin()+src.size()/2, src.end());
      type_conversion(
        ns.follow(src_type.subtype()),
        lower,
        ns.follow(dest_type.subtype()),
        lower_res);
      type_conversion(
        ns.follow(src_type.subtype()),
        upper,
        ns.follow(dest_type.subtype()),
        upper_res);
      INVARIANT(
        lower_res.size() + upper_res.size() == dest_width,
        "lower result bitvector size plus upper result bitvector size shall "
        "equal the destination bitvector size");
      dest=lower_res;
      dest.insert(dest.end(), upper_res.begin(), upper_res.end());
      return false;
    }
  }

  if(src_type.id()==ID_complex)
  {
    INVARIANT(
      dest_type.id() == ID_complex,
      "destination type shall be of complex type when source type is of "
      "complex type");
    if(dest_type.id()==ID_signedbv ||
       dest_type.id()==ID_unsignedbv ||
       dest_type.id()==ID_floatbv ||
       dest_type.id()==ID_fixedbv ||
       dest_type.id()==ID_c_enum ||
       dest_type.id()==ID_c_enum_tag ||
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
  case bvtypet::IS_RANGE:
    if(src_bvtype==bvtypet::IS_UNSIGNED ||
       src_bvtype==bvtypet::IS_SIGNED ||
       src_bvtype==bvtypet::IS_C_BOOL)
    {
      mp_integer dest_from=to_range_type(dest_type).get_from();

      if(dest_from==0)
      {
        // do zero extension
        dest.resize(dest_width);
        for(std::size_t i=0; i<dest.size(); i++)
          dest[i]=(i<src.size()?src[i]:const_literal(false));

        return false;
      }
    }
    else if(src_bvtype==bvtypet::IS_RANGE) // range to range
    {
      mp_integer src_from=to_range_type(src_type).get_from();
      mp_integer dest_from=to_range_type(dest_type).get_from();

      if(dest_from==src_from)
      {
        // do zero extension, if needed
        dest=bv_utils.zero_extension(src, dest_width);
        return false;
      }
      else
      {
        // need to do arithmetic: add src_from-dest_from
        mp_integer offset=src_from-dest_from;
        dest=
          bv_utils.add(
            bv_utils.zero_extension(src, dest_width),
            bv_utils.build_constant(offset, dest_width));
      }

      return false;
    }
    break;

  case bvtypet::IS_FLOAT: // to float
    {
      float_utilst float_utils(prop);

      switch(src_bvtype)
      {
      case bvtypet::IS_FLOAT: // float to float
        // we don't have a rounding mode here,
        // which is why we refuse.
        break;

      case bvtypet::IS_SIGNED: // signed to float
      case bvtypet::IS_C_ENUM:
        float_utils.spec=ieee_float_spect(to_floatbv_type(dest_type));
        dest=float_utils.from_signed_integer(src);
        return false;

      case bvtypet::IS_UNSIGNED: // unsigned to float
      case bvtypet::IS_C_BOOL: // _Bool to float
        float_utils.spec=ieee_float_spect(to_floatbv_type(dest_type));
        dest=float_utils.from_unsigned_integer(src);
        return false;

      case bvtypet::IS_BV:
        INVARIANT(
          src_width == dest_width,
          "source bitvector size shall equal the destination bitvector size");
        dest=src;
        return false;

      default:
        if(src_type.id()==ID_bool)
        {
          // bool to float

          // build a one
          ieee_floatt f(to_floatbv_type(dest_type));
          f.from_integer(1);

          dest=convert_bv(f.to_expr());

          INVARIANT(
            src_width == 1, "bitvector of type boolean shall have width one");

          Forall_literals(it, dest)
            *it=prop.land(*it, src[0]);

          return false;
        }
      }
    }
    break;

  case bvtypet::IS_FIXED:
    if(src_bvtype==bvtypet::IS_FIXED)
    {
      // fixed to fixed

      std::size_t dest_fraction_bits=
        to_fixedbv_type(dest_type).get_fraction_bits();
      std::size_t dest_int_bits=dest_width-dest_fraction_bits;
      std::size_t op_fraction_bits=
        to_fixedbv_type(src_type).get_fraction_bits();
      std::size_t op_int_bits=src_width-op_fraction_bits;

      dest.resize(dest_width);

      // i == position after dot
      // i == 0: first position after dot

      for(std::size_t i=0; i<dest_fraction_bits; i++)
      {
        // position in bv
        std::size_t p=dest_fraction_bits-i-1;

        if(i<op_fraction_bits)
          dest[p]=src[op_fraction_bits-i-1];
        else
          dest[p]=const_literal(false); // zero padding
      }

      for(std::size_t i=0; i<dest_int_bits; i++)
      {
        // position in bv
        std::size_t p=dest_fraction_bits+i;
        INVARIANT(p < dest_width, "bit index shall be within bounds");

        if(i<op_int_bits)
          dest[p]=src[i+op_fraction_bits];
        else
          dest[p]=src[src_width-1]; // sign extension
      }

      return false;
    }
    else if(src_bvtype==bvtypet::IS_BV)
    {
      INVARIANT(
        src_width == dest_width,
        "source bitvector with shall equal the destination bitvector width");
      dest=src;
      return false;
    }
    else if(src_bvtype==bvtypet::IS_UNSIGNED ||
            src_bvtype==bvtypet::IS_SIGNED ||
            src_bvtype==bvtypet::IS_C_BOOL ||
            src_bvtype==bvtypet::IS_C_ENUM)
    {
      // integer to fixed

      std::size_t dest_fraction_bits=
        to_fixedbv_type(dest_type).get_fraction_bits();

      for(std::size_t i=0; i<dest_fraction_bits; i++)
        dest.push_back(const_literal(false)); // zero padding

      for(std::size_t i=0; i<dest_width-dest_fraction_bits; i++)
      {
        literalt l;

        if(i<src_width)
          l=src[i];
        else
        {
          if(src_bvtype==bvtypet::IS_SIGNED || src_bvtype==bvtypet::IS_C_ENUM)
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
      std::size_t fraction_bits=
        to_fixedbv_type(dest_type).get_fraction_bits();

      INVARIANT(
        src_width == 1, "bitvector of type boolean shall have width one");

      for(std::size_t i=0; i<dest_width; i++)
      {
        if(i==fraction_bits)
          dest.push_back(src[0]);
        else
          dest.push_back(const_literal(false));
      }

      return false;
    }
    break;

  case bvtypet::IS_UNSIGNED:
  case bvtypet::IS_SIGNED:
  case bvtypet::IS_C_ENUM:
    switch(src_bvtype)
    {
    case bvtypet::IS_FLOAT: // float to integer
      // we don't have a rounding mode here,
      // which is why we refuse.
      break;

    case bvtypet::IS_FIXED: // fixed to integer
      {
        std::size_t op_fraction_bits=
          to_fixedbv_type(src_type).get_fraction_bits();

        for(std::size_t i=0; i<dest_width; i++)
        {
          if(i<src_width-op_fraction_bits)
            dest.push_back(src[i+op_fraction_bits]);
          else
          {
            if(dest_bvtype==bvtypet::IS_SIGNED)
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

    case bvtypet::IS_UNSIGNED: // integer to integer
    case bvtypet::IS_SIGNED:
    case bvtypet::IS_C_ENUM:
    case bvtypet::IS_C_BOOL:
      {
        // We do sign extension for any source type
        // that is signed, independently of the
        // destination type.
        // E.g., ((short)(ulong)(short)-1)==-1
        bool sign_extension=
          src_bvtype==bvtypet::IS_SIGNED || src_bvtype==bvtypet::IS_C_ENUM;

        for(std::size_t i=0; i<dest_width; i++)
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
    // verilog_unsignedbv to signed/unsigned/enum
    case bvtypet::IS_VERILOG_UNSIGNED:
      {
        for(std::size_t i=0; i<dest_width; i++)
        {
          std::size_t src_index=i*2; // we take every second bit

          if(src_index<src_width)
            dest.push_back(src[src_index]);
          else // always zero-extend
            dest.push_back(const_literal(false));
        }

        return false;
      }
      break;

    case bvtypet::IS_VERILOG_SIGNED: // verilog_signedbv to signed/unsigned/enum
      {
        for(std::size_t i=0; i<dest_width; i++)
        {
          std::size_t src_index=i*2; // we take every second bit

          if(src_index<src_width)
            dest.push_back(src[src_index]);
          else // always sign-extend
            dest.push_back(src.back());
        }

        return false;
      }
      break;

    default:
      if(src_type.id()==ID_bool)
      {
        // bool to integer

        INVARIANT(
          src_width == 1, "bitvector of type boolean shall have width one");

        for(std::size_t i=0; i<dest_width; i++)
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

  case bvtypet::IS_VERILOG_UNSIGNED:
    if(src_bvtype==bvtypet::IS_UNSIGNED ||
       src_bvtype==bvtypet::IS_C_BOOL ||
       src_type.id()==ID_bool)
    {
      for(std::size_t i=0, j=0; i<dest_width; i+=2, j++)
      {
        if(j<src_width)
          dest.push_back(src[j]);
        else
          dest.push_back(const_literal(false));

        dest.push_back(const_literal(false));
      }

      return false;
    }
    else if(src_bvtype==bvtypet::IS_SIGNED)
    {
      for(std::size_t i=0, j=0; i<dest_width; i+=2, j++)
      {
        if(j<src_width)
          dest.push_back(src[j]);
        else
          dest.push_back(src.back());

        dest.push_back(const_literal(false));
      }

      return false;
    }
    else if(src_bvtype==bvtypet::IS_VERILOG_UNSIGNED)
    {
      // verilog_unsignedbv to verilog_unsignedbv
      dest=src;

      if(dest_width<src_width)
        dest.resize(dest_width);
      else
      {
        dest=src;
        while(dest.size()<dest_width)
        {
          dest.push_back(const_literal(false));
          dest.push_back(const_literal(false));
        }
      }
      return false;
    }
    break;

  case bvtypet::IS_BV:
    INVARIANT(
      src_width == dest_width,
      "source bitvector width shall equal the destination bitvector width");
    dest=src;
    return false;

  case bvtypet::IS_C_BOOL:
    dest.resize(dest_width, const_literal(false));

    if(src_bvtype==bvtypet::IS_FLOAT)
    {
      float_utilst float_utils(prop, to_floatbv_type(src_type));
      dest[0]=!float_utils.is_zero(src);
    }
    else if(src_bvtype==bvtypet::IS_C_BOOL)
      dest[0]=src[0];
    else
      dest[0]=!bv_utils.is_zero(src);

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
      const struct_typet &dest_struct=to_struct_type(dest_type);

      if(src_type.id()==ID_struct)
      {
        // we do subsets

        dest.resize(dest_width, const_literal(false));

        const struct_typet &op_struct=to_struct_type(src_type);

        const struct_typet::componentst &dest_comp=
          dest_struct.components();

        const struct_typet::componentst &op_comp=
          op_struct.components();

        // build offset maps
        const offset_mapt op_offsets = build_offset_map(op_struct);
        const offset_mapt dest_offsets = build_offset_map(dest_struct);

        // build name map
        typedef std::map<irep_idt, std::size_t> op_mapt;
        op_mapt op_map;

        for(std::size_t i=0; i<op_comp.size(); i++)
          op_map[op_comp[i].get_name()]=i;

        // now gather required fields
        for(std::size_t i=0;
            i<dest_comp.size();
            i++)
        {
          std::size_t offset=dest_offsets[i];
          std::size_t comp_width=boolbv_width(dest_comp[i].type());
          if(comp_width==0)
            continue;

          op_mapt::const_iterator it=
            op_map.find(dest_comp[i].get_name());

          if(it==op_map.end())
          {
            // not found

            // filling with free variables
            for(std::size_t j=0; j<comp_width; j++)
              dest[offset+j]=prop.new_variable();
          }
          else
          {
            // found
            if(dest_comp[i].type()!=dest_comp[it->second].type())
            {
              // filling with free variables
              for(std::size_t j=0; j<comp_width; j++)
                dest[offset+j]=prop.new_variable();
            }
            else
            {
              std::size_t op_offset=op_offsets[it->second];
              for(std::size_t j=0; j<comp_width; j++)
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

/// conversion from bitvector types to boolean
literalt boolbvt::convert_typecast(const typecast_exprt &expr)
{
  if(expr.op().type().id() == ID_range)
  {
    mp_integer from = string2integer(expr.op().type().get_string(ID_from));
    mp_integer to = string2integer(expr.op().type().get_string(ID_to));

    if(from==1 && to==1)
      return const_literal(true);
    else if(from==0 && to==0)
      return const_literal(false);
  }

  const bvt &bv = convert_bv(expr.op());

  if(!bv.empty())
    return prop.lor(bv);

  return SUB::convert_rest(expr);
}
