/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr_lowering.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>

#include "flatten_byte_extract_exceptions.h"

// clang-format off

/// rewrite an object into its individual bytes
/// \par parameters: src  object to unpack
/// little_endian  true, iff assumed endianness is little-endian
/// max_bytes  if not nil, use as upper bound of the number of bytes to unpack
/// ns  namespace for type lookups
/// \return array of bytes in the sequence found in memory
/// \throws flatten_byte_extract_exceptiont Raised is unable to unpack the
/// object because of either non constant size, byte misalignment or
/// non-constant component width.
static exprt unpack_rec(
  const exprt &src,
  bool little_endian,
  const exprt &max_bytes,
  const namespacet &ns,
  bool unpack_byte_array=false)
{
  array_exprt array(
    array_typet(unsignedbv_typet(8), from_integer(0, size_type())));

  // endianness_mapt should be the point of reference for mapping out
  // endianness, but we need to work on elements here instead of
  // individual bits

  if(src.type().id()==ID_array)
  {
    const array_typet &array_type=to_array_type(src.type());
    const typet &subtype=array_type.subtype();

    auto element_width = pointer_offset_bits(subtype, ns);
    CHECK_RETURN(element_width.has_value());

    // this probably doesn't really matter
    #if 0
    INVARIANT(
      element_width > 0,
      "element width of array should be constant",
      irep_pretty_diagnosticst(src.type()));

    INVARIANT(
      element_width % 8 == 0,
      "elements in array should be byte-aligned",
      irep_pretty_diagnosticst(src.type()));
    #endif

    if(!unpack_byte_array && *element_width == 8)
      return src;

    mp_integer num_elements;
    if(to_integer(max_bytes, num_elements) &&
       to_integer(array_type.size(), num_elements))
    {
      throw non_const_array_sizet(array_type, max_bytes);
    }

    // all array members will have the same structure; do this just
    // once and then replace the dummy symbol by a suitable index
    // expression in the loop below
    symbol_exprt dummy(ID_C_incomplete, subtype);
    exprt sub=unpack_rec(dummy, little_endian, max_bytes, ns, true);

    for(mp_integer i=0; i<num_elements; ++i)
    {
      index_exprt index(src, from_integer(i, index_type()));
      replace_symbolt replace;
      replace.insert(dummy, index);

      for(const auto &op : sub.operands())
      {
        exprt new_op=op;
        replace(new_op);
        simplify(new_op, ns);
        array.copy_to_operands(new_op);
      }
    }
  }
  else if(ns.follow(src.type()).id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(ns.follow(src.type()));
    const struct_typet::componentst &components=struct_type.components();

    for(const auto &comp : components)
    {
      auto element_width = pointer_offset_bits(comp.type(), ns);

      // the next member would be misaligned, abort
      if(
        !element_width.has_value() || *element_width == 0 ||
        *element_width % 8 != 0)
      {
        throw non_byte_alignedt(struct_type, comp, *element_width);
      }

      member_exprt member(src, comp.get_name(), comp.type());
      exprt sub=unpack_rec(member, little_endian, max_bytes, ns, true);

      for(const auto& op : sub.operands())
        array.copy_to_operands(op);
    }
  }
  else if(src.type().id()!=ID_empty)
  {
    // a basic type; we turn that into extractbits while considering
    // endianness
    auto bits_opt = pointer_offset_bits(src.type(), ns);
    mp_integer bits;

    if(bits_opt.has_value())
      bits = *bits_opt;
    else
    {
      if(to_integer(max_bytes, bits))
      {
        throw non_constant_widtht(src, max_bytes);
      }
      else
        bits*=8;
    }

    for(mp_integer i=0; i<bits; i+=8)
    {
      extractbits_exprt extractbits(
        src,
        from_integer(i+7, index_type()),
        from_integer(i, index_type()),
        unsignedbv_typet(8));

      if(little_endian)
        array.copy_to_operands(extractbits);
      else
        array.operands().insert(array.operands().begin(), extractbits);
    }
  }

  to_array_type(array.type()).size()=
    from_integer(array.operands().size(), size_type());

  return std::move(array);
}

/// rewrite byte extraction from an array to byte extraction from a
/// concatenation of array index expressions
exprt lower_byte_extract(const byte_extract_exprt &src, const namespacet &ns)
{
  // General notes about endianness and the bit-vector conversion:
  // A single byte with value 0b10001000 is stored (in irept) as
  // exactly this string literal, and its bit-vector encoding will be
  // bvt bv={0,0,0,1,0,0,0,1}, i.e., bv[0]==0 and bv[7]==1
  //
  // A multi-byte value like x=256 would be:
  // - little-endian storage: ((char*)&x)[0]==0, ((char*)&x)[1]==1
  // - big-endian storage:    ((char*)&x)[0]==1, ((char*)&x)[1]==0
  // - irept representation: 0000000100000000
  // - bvt: {0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0}
  //         <... 8bits ...> <... 8bits ...>
  //
  // An array {0, 1} will be encoded as bvt bv={0,1}, i.e., bv[1]==1
  // concatenation(0, 1) will yield a bvt bv={1,0}, i.e., bv[1]==0
  //
  // The semantics of byte_extract(endianness, op, offset, T) is:
  // interpret ((char*)&op)+offset as the endianness-ordered storage
  // of an object of type T at address ((char*)&op)+offset
  // For some T x, byte_extract(endianness, x, 0, T) must yield x.
  //
  // byte_extract for a composite type T or an array will interpret
  // the individual subtypes with suitable endianness; the overall
  // order of components is not affected by endianness.
  //
  // Examples:
  // unsigned char A[4];
  // byte_extract_little_endian(A, 0, unsigned short) requests that
  // A[0],A[1] be interpreted as the storage of an unsigned short with
  // A[1] being the most-significant byte; byte_extract_big_endian for
  // the same operands will select A[0] as the most-significant byte.
  //
  // int A[2] = {0x01020304,0xDEADBEEF}
  // byte_extract_big_endian(A, 0, short) should yield 0x0102
  // byte_extract_little_endian(A, 0, short) should yield 0x0304
  // To obtain this we first compute byte arrays while taking into
  // account endianness:
  // big-endian byte representation: {01,02,03,04,DE,AB,BE,EF}
  // little-endian byte representation: {04,03,02,01,EF,BE,AB,DE}
  // We extract the relevant bytes starting from ((char*)A)+0:
  // big-endian: {01,02}; little-endian: {04,03}
  // Finally we place them in the appropriate byte order as indicated
  // by endianness:
  // big-endian: (short)concatenation(01,02)=0x0102
  // little-endian: (short)concatenation(03,04)=0x0304

  PRECONDITION(
    src.id() == ID_byte_extract_little_endian ||
    src.id() == ID_byte_extract_big_endian);
  const bool little_endian = src.id() == ID_byte_extract_little_endian;

  // determine an upper bound of the number of bytes we might need
  exprt upper_bound=size_of_expr(src.type(), ns);
  if(upper_bound.is_not_nil())
    upper_bound=
      simplify_expr(
        plus_exprt(
          upper_bound,
          typecast_exprt(src.offset(), upper_bound.type())),
        ns);

  byte_extract_exprt unpacked(src);
  unpacked.op()=
    unpack_rec(src.op(), little_endian, upper_bound, ns);

  if(src.type().id()==ID_array)
  {
    const array_typet &array_type=to_array_type(src.type());
    const typet &subtype=array_type.subtype();

    auto element_width = pointer_offset_bits(subtype, ns);
    mp_integer num_elements;
    // TODO: consider ways of dealing with arrays of unknown subtype
    // size or with a subtype size that does not fit byte boundaries
    if(
      element_width.has_value() && *element_width >= 1 &&
      *element_width % 8 == 0 && to_integer(array_type.size(), num_elements))
    {
      array_exprt array(array_type);

      for(mp_integer i=0; i<num_elements; ++i)
      {
        plus_exprt new_offset(
          unpacked.offset(),
          from_integer(i * (*element_width), unpacked.offset().type()));

        byte_extract_exprt tmp(unpacked);
        tmp.type()=subtype;
        tmp.offset()=new_offset;

        array.copy_to_operands(lower_byte_extract(tmp, ns));
      }

      return simplify_expr(array, ns);
    }
  }
  else if(ns.follow(src.type()).id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(ns.follow(src.type()));
    const struct_typet::componentst &components=struct_type.components();

    bool failed=false;
    struct_exprt s({}, src.type());

    for(const auto &comp : components)
    {
      auto element_width = pointer_offset_bits(comp.type(), ns);

      // the next member would be misaligned, abort
      if(
        !element_width.has_value() || *element_width == 0 ||
        *element_width % 8 != 0)
      {
        failed=true;
        break;
      }

      plus_exprt new_offset(
        unpacked.offset(),
        typecast_exprt(
          member_offset_expr(struct_type, comp.get_name(), ns),
          unpacked.offset().type()));

      byte_extract_exprt tmp(unpacked);
      tmp.type()=comp.type();
      tmp.offset()=new_offset;

      s.add_to_operands(std::move(tmp));
    }

    if(!failed)
      return simplify_expr(s, ns);
  }

  const exprt &root=unpacked.op();
  const exprt &offset=unpacked.offset();

  const array_typet &array_type=to_array_type(root.type());
  const typet &subtype=array_type.subtype();

  auto subtype_bits = pointer_offset_bits(subtype, ns);

  DATA_INVARIANT(
    subtype_bits.has_value() && *subtype_bits == 8,
    "offset bits are byte aligned");

  auto size_bits = pointer_offset_bits(unpacked.type(), ns);
  if(!size_bits.has_value())
  {
    auto op0_bits = pointer_offset_bits(unpacked.op().type(), ns);
    if(op0_bits.has_value())
    {
      throw non_const_byte_extraction_sizet(unpacked);
    }
    else
      size_bits=op0_bits;
  }

  mp_integer num_elements =
    (*size_bits) / 8 + (((*size_bits) % 8 == 0) ? 0 : 1);

  // get 'width'-many bytes, and concatenate
  const std::size_t width_bytes = numeric_cast_v<std::size_t>(num_elements);
  exprt::operandst op;
  op.reserve(width_bytes);

  for(std::size_t i=0; i<width_bytes; i++)
  {
    // the most significant byte comes first in the concatenation!
    std::size_t offset_int=
      little_endian?(width_bytes-i-1):i;

    plus_exprt offset_i(from_integer(offset_int, offset.type()), offset);
    index_exprt index_expr(root, offset_i);
    op.push_back(index_expr);
  }

  if(width_bytes==1)
    return simplify_expr(typecast_exprt(op.front(), src.type()), ns);
  else // width_bytes>=2
  {
    concatenation_exprt concatenation(std::move(op), src.type());
    return simplify_expr(concatenation, ns);
  }
}

static exprt lower_byte_update(
  const byte_update_exprt &src,
  const namespacet &ns,
  bool negative_offset)
{
  const auto element_size_opt = pointer_offset_size(src.value().type(), ns);

  INVARIANT_WITH_DIAGNOSTICS(
    element_size_opt.has_value(),
    "size of type in bytes must be known",
    irep_pretty_diagnosticst(src));

  const mp_integer &element_size = *element_size_opt;

  if(src.op0().type().id()==ID_array)
  {
    const array_typet &array_type=to_array_type(src.op0().type());
    const typet &subtype=array_type.subtype();

    // array of bitvectors?
    if(subtype.id()==ID_unsignedbv ||
       subtype.id()==ID_signedbv ||
       subtype.id()==ID_floatbv ||
       subtype.id()==ID_c_bool ||
       subtype.id()==ID_pointer)
    {
      auto sub_size_opt = pointer_offset_size(subtype, ns);

      INVARIANT(
        sub_size_opt.has_value(),
        "bit width (rounded to full bytes) of subtype must be known");

      const mp_integer &sub_size = *sub_size_opt;

      // byte array?
      if(sub_size==1)
      {
        // apply 'array-update-with' element_size times
        exprt result = src.op();

        for(mp_integer i=0; i<element_size; ++i)
        {
          exprt i_expr = from_integer(i, src.offset().type());

          exprt new_value;

          if(i==0 && element_size==1) // bytes?
          {
            new_value = src.value();
            if(new_value.type()!=subtype)
              new_value.make_typecast(subtype);
          }
          else
          {
            INVARIANT(
              src.id() == ID_byte_update_little_endian ||
                src.id() == ID_byte_update_big_endian,
              "byte update expression should either be little or big endian");

            byte_extract_exprt byte_extract_expr(
              src.id() == ID_byte_update_little_endian
                ? ID_byte_extract_little_endian
                : ID_byte_extract_big_endian,
              src.value(),
              i_expr,
              subtype);

            new_value=lower_byte_extract(byte_extract_expr, ns);
          }

          const plus_exprt where(src.offset(), i_expr);

          with_exprt with_expr(result, where, new_value);
          with_expr.type()=src.type();

          result.swap(with_expr);
        }

        return simplify_expr(result, ns);
      }
      else // sub_size!=1
      {
        exprt result = src.op();

        // Number of potentially affected array cells:
        mp_integer num_elements=
          element_size/sub_size+((element_size%sub_size==0)?1:2);

        const auto &offset_type = src.offset().type();
        exprt zero_offset=from_integer(0, offset_type);

        exprt sub_size_expr=from_integer(sub_size, offset_type);
        exprt element_size_expr=from_integer(element_size, offset_type);

        // First potentially affected cell:
        div_exprt first_cell(src.offset(), sub_size_expr);

        for(mp_integer i=0; i<num_elements; ++i)
        {
          plus_exprt cell_index(first_cell, from_integer(i, offset_type));
          mult_exprt cell_offset(cell_index, sub_size_expr);
          index_exprt old_cell_value(src.op(), cell_index, subtype);
          bool is_first_cell=i==0;
          bool is_last_cell=i==num_elements-1;

          exprt new_value;
          exprt stored_value_offset;
          if(element_size<=sub_size)
          {
            new_value = src.value();
            stored_value_offset=zero_offset;
          }
          else
          {
            // Offset to retrieve from the stored value: make sure not to
            // ask for anything out of range; in the first- or last-cell cases
            // we will adjust the offset in the byte_update call below.
            if(is_first_cell)
              stored_value_offset=zero_offset;
            else if(is_last_cell)
              stored_value_offset=
                from_integer(element_size-sub_size, offset_type);
            else
              stored_value_offset = minus_exprt(cell_offset, src.offset());

            INVARIANT(
              src.id() == ID_byte_update_little_endian ||
                src.id() == ID_byte_update_big_endian,
              "byte update expression should either be little or big endian");

            byte_extract_exprt byte_extract_expr(
              src.id() == ID_byte_update_little_endian
                ? ID_byte_extract_little_endian
                : ID_byte_extract_big_endian,
                src.value(), stored_value_offset,
              element_size < sub_size ? src.value().type() : subtype);

            new_value=lower_byte_extract(byte_extract_expr, ns);
          }

          // Where does the value we just extracted align in this cell?
          // This value might be negative, indicating only the most-significant
          // bytes should be written, to the least-significant bytes of the
          // target array cell.
          exprt overwrite_offset;
          if(is_first_cell)
            overwrite_offset = mod_exprt(src.offset(), sub_size_expr);
          else if(is_last_cell)
          {
            // This is intentionally negated; passing is_last_cell
            // to flatten below leads to it being negated again later.
            overwrite_offset = minus_exprt(
              minus_exprt(cell_offset, src.offset()), stored_value_offset);
          }
          else
            overwrite_offset=zero_offset;

          byte_update_exprt byte_update_expr(
            src.id(),
            old_cell_value,
            overwrite_offset,
            new_value);

          // Call recursively, the array is gone!
          // The last parameter indicates that the
          exprt flattened_byte_update_expr=
            lower_byte_update(byte_update_expr, ns, is_last_cell);

          with_exprt with_expr(
            result, cell_index, flattened_byte_update_expr);

          result=with_expr;
        }

        return simplify_expr(result, ns);
      }
    }
    else
    {
      PRECONDITION_WITH_DIAGNOSTICS(
        false,
        "flatten_byte_update can only do arrays of scalars right now",
        subtype.id_string());
    }
  }
  else if(src.op0().type().id()==ID_signedbv ||
          src.op0().type().id()==ID_unsignedbv ||
          src.op0().type().id()==ID_floatbv ||
          src.op0().type().id()==ID_c_bool ||
          src.op0().type().id()==ID_pointer)
  {
    // do a shift, mask and OR
    const auto type_width = pointer_offset_bits(src.op0().type(), ns);
    CHECK_RETURN(type_width.has_value() && *type_width > 0);
    const std::size_t width = numeric_cast_v<std::size_t>(*type_width);

    INVARIANT(
      element_size * 8 <= width,
      "element bit width must not be larger than width indicated by type");

    // build mask
    exprt mask=
      from_integer(power(2, element_size*8)-1, unsignedbv_typet(width));

    // zero-extend the value, but only if needed
    exprt value_extended;

    if(width > element_size * 8)
      value_extended = concatenation_exprt(
        from_integer(
          0,
          unsignedbv_typet(
            width - numeric_cast_v<std::size_t>(element_size) * 8)),
        src.value(),
        src.op0().type());
    else
      value_extended = src.value();

    const typet &offset_type = src.offset().type();
    mult_exprt offset_times_eight(src.offset(), from_integer(8, offset_type));

    binary_predicate_exprt offset_ge_zero(
      offset_times_eight,
      ID_ge,
      from_integer(0, offset_type));

    // Shift the mask and value.
    // Note either shift might discard some of the new value's bits.
    exprt mask_shifted;
    exprt value_shifted;
    if(negative_offset)
    {
      // In this case we shift right, to mask out higher addresses
      // rather than left to mask out lower ones as usual.
      mask_shifted=lshr_exprt(mask, offset_times_eight);
      value_shifted=lshr_exprt(value_extended, offset_times_eight);
    }
    else
    {
      mask_shifted=shl_exprt(mask, offset_times_eight);
      value_shifted=shl_exprt(value_extended, offset_times_eight);
    }

    // original_bits &= ~mask
    bitand_exprt bitand_expr(src.op(), bitnot_exprt(mask_shifted));

    // original_bits |= newvalue
    bitor_exprt bitor_expr(bitand_expr, value_shifted);

    return simplify_expr(bitor_expr, ns);
  }
  else
  {
    PRECONDITION_WITH_DIAGNOSTICS(
      false,
      "flatten_byte_update can only do arrays and scalars right now",
      src.op0().type().id_string());
  }
}

static exprt lower_byte_update(
  const byte_update_exprt &src,
  const namespacet &ns)
{
  return lower_byte_update(src, ns, false);
}

bool has_byte_operator(const exprt &src)
{
  if(src.id()==ID_byte_update_little_endian ||
     src.id()==ID_byte_update_big_endian ||
     src.id()==ID_byte_extract_little_endian ||
     src.id()==ID_byte_extract_big_endian)
    return true;

  forall_operands(it, src)
    if(has_byte_operator(*it))
      return true;

  return false;
}

exprt lower_byte_operators(const exprt &src, const namespacet &ns)
{
  exprt tmp=src;

  // destroys any sharing, should use hash table
  Forall_operands(it, tmp)
  {
    *it = lower_byte_operators(*it, ns);
  }

  if(src.id()==ID_byte_update_little_endian ||
     src.id()==ID_byte_update_big_endian)
    return lower_byte_update(to_byte_update_expr(tmp), ns);
  else if(src.id()==ID_byte_extract_little_endian ||
          src.id()==ID_byte_extract_big_endian)
    return lower_byte_extract(to_byte_extract_expr(tmp), ns);
  else
    return tmp;
}
// clang-format on
