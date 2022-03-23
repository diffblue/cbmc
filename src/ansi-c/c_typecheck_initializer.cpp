/*******************************************************************\

Module: ANSI-C Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Conversion / Type Checking

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/expr_initializer.h>
#include <util/prefix.h>
#include <util/std_types.h>
#include <util/string_constant.h>

#include "anonymous_member.h"
#include "c_typecheck_base.h"
#include "type2name.h"

#include <cassert>

void c_typecheck_baset::do_initializer(
  exprt &initializer,
  const typet &type,
  bool force_constant)
{
  exprt result=do_initializer_rec(initializer, type, force_constant);

  if(type.id()==ID_array)
  {
    const typet &result_type = result.type();
    DATA_INVARIANT(result_type.id()==ID_array &&
                   to_array_type(result_type).size().is_not_nil(),
                   "any array must have a size");

    // we don't allow initialisation with symbols of array type
    if(
      result.id() != ID_array && result.id() != ID_array_of &&
      result.id() != ID_compound_literal)
    {
      error().source_location = result.source_location();
      error() << "invalid array initializer " << to_string(result)
              << eom;
      throw 0;
    }
  }

  initializer=result;
}

/// initialize something of type `type' with given value `value'
exprt c_typecheck_baset::do_initializer_rec(
  const exprt &value,
  const typet &type,
  bool force_constant)
{
  const typet &full_type=follow(type);

  if(
    (full_type.id() == ID_struct || full_type.id() == ID_union) &&
    to_struct_union_type(full_type).is_incomplete())
  {
    error().source_location = value.source_location();
    error() << "type '" << to_string(type)
            << "' is still incomplete -- cannot initialize" << eom;
    throw 0;
  }

  if(value.id()==ID_initializer_list)
    return do_initializer_list(value, type, force_constant);

  if(
    value.id() == ID_array && value.get_bool(ID_C_string_constant) &&
    full_type.id() == ID_array &&
    (to_array_type(full_type).element_type().id() == ID_signedbv ||
     to_array_type(full_type).element_type().id() == ID_unsignedbv) &&
    to_bitvector_type(to_array_type(full_type).element_type()).get_width() ==
      to_bitvector_type(to_array_type(value.type()).element_type()).get_width())
  {
    exprt tmp=value;

    // adjust char type
    to_array_type(tmp.type()).element_type() =
      to_array_type(full_type).element_type();

    Forall_operands(it, tmp)
      it->type() = to_array_type(full_type).element_type();

    if(full_type.id()==ID_array &&
       to_array_type(full_type).is_complete())
    {
      const auto &array_type = to_array_type(full_type);

      // check size
      const auto array_size = numeric_cast<mp_integer>(array_type.size());
      if(!array_size.has_value())
      {
        error().source_location = value.source_location();
        error() << "array size needs to be constant, got "
                << to_string(array_type.size()) << eom;
        throw 0;
      }

      if(*array_size < 0)
      {
        error().source_location = value.source_location();
        error() << "array size must not be negative" << eom;
        throw 0;
      }

      if(mp_integer(tmp.operands().size()) > *array_size)
      {
        // cut off long strings. gcc does a warning for this
        tmp.operands().resize(numeric_cast_v<std::size_t>(*array_size));
        tmp.type()=type;
      }
      else if(mp_integer(tmp.operands().size()) < *array_size)
      {
        // fill up
        tmp.type()=type;
        const auto zero = zero_initializer(
          array_type.element_type(), value.source_location(), *this);
        if(!zero.has_value())
        {
          error().source_location = value.source_location();
          error() << "cannot zero-initialize array with subtype '"
                  << to_string(array_type.element_type()) << "'" << eom;
          throw 0;
        }
        tmp.operands().resize(numeric_cast_v<std::size_t>(*array_size), *zero);
      }
    }

    return tmp;
  }

  if(
    value.id() == ID_string_constant && full_type.id() == ID_array &&
    (to_array_type(full_type).element_type().id() == ID_signedbv ||
     to_array_type(full_type).element_type().id() == ID_unsignedbv) &&
    to_bitvector_type(to_array_type(full_type).element_type()).get_width() ==
      char_type().get_width())
  {
    // will go away, to be replaced by the above block

    string_constantt tmp1=to_string_constant(value);
    // adjust char type
    tmp1.type().subtype() = to_array_type(full_type).element_type();

    exprt tmp2=tmp1.to_array_expr();

    if(full_type.id()==ID_array &&
       to_array_type(full_type).is_complete())
    {
      // check size
      const auto array_size =
        numeric_cast<mp_integer>(to_array_type(full_type).size());
      if(!array_size.has_value())
      {
        error().source_location = value.source_location();
        error() << "array size needs to be constant, got "
                << to_string(to_array_type(full_type).size()) << eom;
        throw 0;
      }

      if(*array_size < 0)
      {
        error().source_location = value.source_location();
        error() << "array size must not be negative" << eom;
        throw 0;
      }

      if(mp_integer(tmp2.operands().size()) > *array_size)
      {
        // cut off long strings. gcc does a warning for this
        tmp2.operands().resize(numeric_cast_v<std::size_t>(*array_size));
        tmp2.type()=type;
      }
      else if(mp_integer(tmp2.operands().size()) < *array_size)
      {
        // fill up
        tmp2.type()=type;
        const auto zero = zero_initializer(
          to_array_type(full_type).element_type(),
          value.source_location(),
          *this);
        if(!zero.has_value())
        {
          error().source_location = value.source_location();
          error() << "cannot zero-initialize array with subtype '"
                  << to_string(to_array_type(full_type).element_type()) << "'"
                  << eom;
          throw 0;
        }
        tmp2.operands().resize(numeric_cast_v<std::size_t>(*array_size), *zero);
      }
    }

    return tmp2;
  }

  if(full_type.id()==ID_array &&
     to_array_type(full_type).size().is_nil())
  {
    error().source_location = value.source_location();
    error() << "type '" << to_string(full_type)
            << "' cannot be initialized with '" << to_string(value) << "'"
            << eom;
    throw 0;
  }

  if(value.id()==ID_designated_initializer)
  {
    error().source_location = value.source_location();
    error() << "type '" << to_string(full_type)
            << "' cannot be initialized with designated initializer" << eom;
    throw 0;
  }

  exprt result=value;
  implicit_typecast(result, type);
  return result;
}

void c_typecheck_baset::do_initializer(symbolt &symbol)
{
  // this one doesn't need initialization
  if(has_prefix(id2string(symbol.name), CPROVER_PREFIX "constant_infinity"))
    return;

  if(symbol.is_type)
    return;

  if(symbol.value.is_not_nil())
  {
    typecheck_expr(symbol.value);
    do_initializer(symbol.value, symbol.type, true);

    // A flexible array may have been initialized, which entails a type change.
    // Note that the type equality test is important: we want to preserve
    // annotations like typedefs or const-ness when the type is otherwise the
    // same.
    if(!symbol.is_macro && symbol.type != symbol.value.type())
      symbol.type = symbol.value.type();
  }

  if(symbol.is_macro)
    make_constant(symbol.value);
}

void c_typecheck_baset::designator_enter(
  const typet &type,
  designatort &designator)
{
  designatort::entryt entry(type);

  const typet &full_type=follow(type);

  if(full_type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(full_type);

    entry.size=struct_type.components().size();
    entry.subtype.make_nil();
    // only a top-level struct may end with a variable-length array
    entry.vla_permitted=designator.empty();

    for(const auto &c : struct_type.components())
    {
      if(c.type().id() != ID_code && !c.get_is_padding())
      {
        entry.subtype = c.type();
        break;
      }

      ++entry.index;
    }
  }
  else if(full_type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(full_type);

    if(union_type.components().empty())
    {
      entry.size=0;
      entry.subtype.make_nil();
    }
    else
    {
      // The default is to initialize using the first member of the
      // union.
      entry.size=1;
      entry.subtype=union_type.components().front().type();
    }
  }
  else if(full_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(full_type);

    if(array_type.size().is_nil())
    {
      entry.size=0;
      entry.subtype = array_type.element_type();
    }
    else
    {
      const auto array_size = numeric_cast<mp_integer>(array_type.size());
      if(!array_size.has_value())
      {
        error().source_location = array_type.size().source_location();
        error() << "array has non-constant size '"
                << to_string(array_type.size()) << "'" << eom;
        throw 0;
      }

      entry.size = numeric_cast_v<std::size_t>(*array_size);
      entry.subtype = array_type.element_type();
    }
  }
  else if(full_type.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(full_type);

    const auto vector_size = numeric_cast<mp_integer>(vector_type.size());

    if(!vector_size.has_value())
    {
      error().source_location = vector_type.size().source_location();
      error() << "vector has non-constant size '"
              << to_string(vector_type.size()) << "'" << eom;
      throw 0;
    }

    entry.size = numeric_cast_v<std::size_t>(*vector_size);
    entry.subtype = vector_type.element_type();
  }
  else
    UNREACHABLE;

  designator.push_entry(entry);
}

exprt::operandst::const_iterator c_typecheck_baset::do_designated_initializer(
  exprt &result,
  designatort &designator,
  const exprt &initializer_list,
  exprt::operandst::const_iterator init_it,
  bool force_constant)
{
  // copy the value, we may need to adjust it
  exprt value=*init_it;

  assert(!designator.empty());

  if(value.id()==ID_designated_initializer)
  {
    assert(value.operands().size()==1);

    designator=
      make_designator(
        designator.front().type,
        static_cast<const exprt &>(value.find(ID_designator)));

    assert(!designator.empty());

    // discard the return value
    do_designated_initializer(
      result, designator, value, value.operands().begin(), force_constant);
    return ++init_it;
  }

  exprt *dest=&result;

  // first phase: follow given designator

  for(size_t i=0; i<designator.size(); i++)
  {
    size_t index=designator[i].index;
    const typet &type=designator[i].type;
    const typet &full_type=follow(type);

    if(full_type.id()==ID_array ||
       full_type.id()==ID_vector)
    {
      // zero_initializer may have built an array_of expression for a large
      // array; as we have a designated initializer we need to have an array of
      // individual objects
      if(dest->id() == ID_array_of)
      {
        const array_typet array_type = to_array_type(dest->type());
        const auto array_size = numeric_cast<mp_integer>(array_type.size());
        if(!array_size.has_value())
        {
          error().source_location = value.source_location();
          error() << "cannot zero-initialize array with element type '"
                  << to_string(to_type_with_subtype(full_type).subtype()) << "'"
                  << eom;
          throw 0;
        }
        const exprt zero = to_array_of_expr(*dest).what();
        *dest = array_exprt{{}, array_type};
        dest->operands().resize(numeric_cast_v<std::size_t>(*array_size), zero);
      }

      if(index>=dest->operands().size())
      {
        if(full_type.id()==ID_array &&
           (to_array_type(full_type).size().is_zero() ||
            to_array_type(full_type).size().is_nil()))
        {
          const typet &element_type = to_array_type(full_type).element_type();

          // we are willing to grow an incomplete or zero-sized array --
          // do_initializer_list will fix up the resulting type
          const auto zero =
            zero_initializer(element_type, value.source_location(), *this);
          if(!zero.has_value())
          {
            error().source_location = value.source_location();
            error() << "cannot zero-initialize array with element type '"
                    << to_string(element_type) << "'" << eom;
            throw 0;
          }
          dest->operands().resize(
            numeric_cast_v<std::size_t>(index) + 1, *zero);
        }
        else
        {
          error().source_location = value.source_location();
          error() << "array index designator " << index
                  << " out of bounds (" << dest->operands().size()
                  << ")" << eom;
          throw 0;
        }
      }

      dest = &(dest->operands()[numeric_cast_v<std::size_t>(index)]);
    }
    else if(full_type.id()==ID_struct)
    {
      const struct_typet::componentst &components=
        to_struct_type(full_type).components();

      if(index>=dest->operands().size())
      {
        error().source_location = value.source_location();
        error() << "structure member designator " << index
                << " out of bounds (" << dest->operands().size()
                << ")" << eom;
        throw 0;
      }

      DATA_INVARIANT(index<components.size(),
                     "member designator is bounded by components size");
      DATA_INVARIANT(components[index].type().id()!=ID_code &&
                     !components[index].get_is_padding(),
                     "member designator points at data member");

      dest=&(dest->operands()[index]);
    }
    else if(full_type.id()==ID_union)
    {
      const union_typet &union_type=to_union_type(full_type);

      const union_typet::componentst &components=
        union_type.components();

      if(components.empty())
      {
        error().source_location = value.source_location();
        error() << "union member designator found for empty union" << eom;
        throw 0;
      }
      else if(init_it != initializer_list.operands().begin())
      {
        if(config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
        {
          error().source_location = value.source_location();
          error() << "too many initializers" << eom;
          throw 0;
        }
        else
        {
          warning().source_location = value.source_location();
          warning() << "excess elements in union initializer" << eom;

          return ++init_it;
        }
      }
      else if(index >= components.size())
      {
        error().source_location = value.source_location();
        error() << "union member designator " << index << " out of bounds ("
                << components.size() << ")" << eom;
        throw 0;
      }

      const union_typet::componentt &component = components[index];

      if(
        dest->id() == ID_union &&
        to_union_expr(*dest).get_component_name() == component.get_name())
      {
        // Already right union component. We can initialize multiple submembers,
        // so do not overwrite this.
        dest = &(to_union_expr(*dest).op());
      }
      else if(dest->id() == ID_union)
      {
        // The designated initializer does not initialize the maximum member,
        // which the (default) zero initializer prepared. Replace this by a
        // component-specific initializer; other bytes have an unspecified value
        // (C Standard 6.2.6.1(7)). In practice, objects of static lifetime are
        // fully zero initialized, so we just byte-update on top of the existing
        // zero initializer.
        const auto zero =
          zero_initializer(component.type(), value.source_location(), *this);
        if(!zero.has_value())
        {
          error().source_location = value.source_location();
          error() << "cannot zero-initialize union component of type '"
                  << to_string(component.type()) << "'" << eom;
          throw 0;
        }

        if(current_symbol.is_static_lifetime)
        {
          byte_update_exprt byte_update =
            make_byte_update(*dest, from_integer(0, c_index_type()), *zero);
          byte_update.add_source_location() = value.source_location();
          *dest = std::move(byte_update);
          dest = &(to_byte_update_expr(*dest).op2());
        }
        else
        {
          union_exprt union_expr(component.get_name(), *zero, type);
          union_expr.add_source_location() = value.source_location();
          *dest = std::move(union_expr);
          dest = &(to_union_expr(*dest).op());
        }
      }
      else if(
        dest->id() == ID_byte_update_big_endian ||
        dest->id() == ID_byte_update_little_endian)
      {
        // handle the byte update introduced by an earlier initializer (if
        // current_symbol.is_static_lifetime)
        byte_update_exprt &byte_update = to_byte_update_expr(*dest);
        dest = &byte_update.op2();
      }
    }
    else
      UNREACHABLE;
  }

  // second phase: assign value
  // for this, we may need to go down, adding to the designator

  while(true)
  {
    // see what type we have to initialize

    const typet &type=designator.back().subtype;
    const typet &full_type=follow(type);

    // do we initialize a scalar?
    if(full_type.id()!=ID_struct &&
       full_type.id()!=ID_union &&
       full_type.id()!=ID_array &&
       full_type.id()!=ID_vector)
    {
      // The initializer for a scalar shall be a single expression,
      // * optionally enclosed in braces. *

      if(value.id()==ID_initializer_list &&
         value.operands().size()==1)
      {
        *dest =
          do_initializer_rec(to_unary_expr(value).op(), type, force_constant);
      }
      else
        *dest=do_initializer_rec(value, type, force_constant);

      assert(full_type==follow(dest->type()));

      return ++init_it; // done
    }

    // union? The component in the zero initializer might
    // not be the first one.
    if(full_type.id()==ID_union)
    {
      const union_typet &union_type=to_union_type(full_type);

      const union_typet::componentst &components=
        union_type.components();

      if(!components.empty())
      {
        const union_typet::componentt &component=
          union_type.components().front();

        const auto zero =
          zero_initializer(component.type(), value.source_location(), *this);
        if(!zero.has_value())
        {
          error().source_location = value.source_location();
          error() << "cannot zero-initialize union component of type '"
                  << to_string(component.type()) << "'" << eom;
          throw 0;
        }
        union_exprt union_expr(component.get_name(), *zero, type);
        union_expr.add_source_location()=value.source_location();
        *dest=union_expr;
      }
    }

    // see what initializer we are given
    if(value.id()==ID_initializer_list)
    {
      *dest=do_initializer_rec(value, type, force_constant);
      return ++init_it; // done
    }
    else if(value.id()==ID_string_constant)
    {
      // We stop for initializers that are string-constants,
      // which are like arrays. We only do so if we are to
      // initialize an array of scalars.
      if(
        full_type.id() == ID_array &&
        (to_array_type(full_type).element_type().id() == ID_signedbv ||
         to_array_type(full_type).element_type().id() == ID_unsignedbv))
      {
        *dest=do_initializer_rec(value, type, force_constant);
        return ++init_it; // done
      }
    }
    else if(follow(value.type())==full_type)
    {
      // a struct/union/vector can be initialized directly with
      // an expression of the right type. This doesn't
      // work with arrays, unfortunately.
      if(full_type.id()==ID_struct ||
         full_type.id()==ID_union ||
         full_type.id()==ID_vector)
      {
        *dest=value;
        return ++init_it; // done
      }
    }

    assert(full_type.id()==ID_struct ||
           full_type.id()==ID_union ||
           full_type.id()==ID_array ||
           full_type.id()==ID_vector);

    // we are initializing a compound type, and enter it!
    // this may change the type, full_type might not be valid any more
    const typet dest_type=full_type;
    const bool vla_permitted=designator.back().vla_permitted;
    designator_enter(type, designator);

    // GCC permits (though issuing a warning with -Wall) composite
    // types built from flat initializer lists
    if(dest->operands().empty())
    {
      warning().source_location=value.find_source_location();
      warning() << "initialisation of " << dest_type.id()
                << " requires initializer list, found " << value.id()
                << " instead" << eom;

      // in case of a variable-length array consume all remaining
      // initializer elements
      if(vla_permitted &&
         dest_type.id()==ID_array &&
         (to_array_type(dest_type).size().is_zero() ||
          to_array_type(dest_type).size().is_nil()))
      {
        value.id(ID_initializer_list);
        value.operands().clear();
        for( ; init_it!=initializer_list.operands().end(); ++init_it)
          value.copy_to_operands(*init_it);
        *dest=do_initializer_rec(value, dest_type, force_constant);

        return init_it;
      }
      else
      {
        error().source_location = value.source_location();
        error() << "cannot initialize type '" << to_string(dest_type)
                << "' using value '" << to_string(value) << "'" << eom;
        throw 0;
      }
    }

    dest = &(to_multi_ary_expr(*dest).op0());

    // we run into another loop iteration
  }

  return ++init_it;
}

void c_typecheck_baset::increment_designator(designatort &designator)
{
  assert(!designator.empty());

  while(true)
  {
    designatort::entryt &entry=designator[designator.size()-1];
    const typet &full_type=follow(entry.type);

    entry.index++;

    if(full_type.id()==ID_array &&
       to_array_type(full_type).size().is_nil())
      return; // we will keep going forever

    if(full_type.id()==ID_struct &&
       entry.index<entry.size)
    {
      // need to adjust subtype
      const struct_typet &struct_type=
        to_struct_type(full_type);
      const struct_typet::componentst &components=
        struct_type.components();
      assert(components.size()==entry.size);

      // we skip over any padding or code
      // we also skip over anonymous members
      while(entry.index < entry.size &&
            (components[entry.index].get_is_padding() ||
             (components[entry.index].get_anonymous() &&
              components[entry.index].type().id() != ID_struct_tag &&
              components[entry.index].type().id() != ID_union_tag) ||
             components[entry.index].type().id() == ID_code))
      {
        entry.index++;
      }

      if(entry.index<entry.size)
        entry.subtype=components[entry.index].type();
    }

    if(entry.index<entry.size)
      return; // done

    if(designator.size()==1)
      return; // done

    // pop entry
    designator.pop_entry();

    assert(!designator.empty());
  }
}

designatort c_typecheck_baset::make_designator(
  const typet &src_type,
  const exprt &src)
{
  assert(!src.operands().empty());

  typet type=src_type;
  designatort designator;

  forall_operands(it, src)
  {
    const exprt &d_op=*it;
    designatort::entryt entry(type);
    const typet &full_type=follow(entry.type);

    if(full_type.id()==ID_array)
    {
      if(d_op.id()!=ID_index)
      {
        error().source_location = d_op.source_location();
        error() << "expected array index designator" << eom;
        throw 0;
      }

      exprt tmp_index = to_unary_expr(d_op).op();
      make_constant_index(tmp_index);

      mp_integer index, size;

      if(to_integer(to_constant_expr(tmp_index), index))
      {
        error().source_location = to_unary_expr(d_op).op().source_location();
        error() << "expected constant array index designator" << eom;
        throw 0;
      }

      if(to_array_type(full_type).size().is_nil())
        size=0;
      else if(
        const auto size_opt =
          numeric_cast<mp_integer>(to_array_type(full_type).size()))
        size = *size_opt;
      else
      {
        error().source_location = to_unary_expr(d_op).op().source_location();
        error() << "expected constant array size" << eom;
        throw 0;
      }

      entry.index = numeric_cast_v<std::size_t>(index);
      entry.size = numeric_cast_v<std::size_t>(size);
      entry.subtype = to_array_type(full_type).element_type();
    }
    else if(full_type.id()==ID_struct ||
            full_type.id()==ID_union)
    {
      const struct_union_typet &struct_union_type=
        to_struct_union_type(full_type);

      if(d_op.id()!=ID_member)
      {
        error().source_location = d_op.source_location();
        error() << "expected member designator" << eom;
        throw 0;
      }

      const irep_idt &component_name=d_op.get(ID_component_name);

      if(struct_union_type.has_component(component_name))
      {
        // a direct member
        entry.index=struct_union_type.component_number(component_name);
        entry.size=struct_union_type.components().size();
        entry.subtype=struct_union_type.components()[entry.index].type();
      }
      else
      {
        // We will search for anonymous members,
        // in a loop. This isn't supported by gcc, but icc does allow it.

        bool found=false, repeat;
        typet tmp_type=entry.type;

        do
        {
          repeat=false;
          std::size_t number = 0;
          const struct_union_typet::componentst &components=
            to_struct_union_type(follow(tmp_type)).components();

          for(const auto &c : components)
          {
            if(c.get_name() == component_name)
            {
              // done!
              entry.index=number;
              entry.size=components.size();
              entry.subtype = c.type();
              entry.type=tmp_type;
            }
            else if(
              c.get_anonymous() &&
              (c.type().id() == ID_struct_tag ||
               c.type().id() == ID_union_tag) &&
              has_component_rec(c.type(), component_name, *this))
            {
              entry.index=number;
              entry.size=components.size();
              entry.subtype = c.type();
              entry.type=tmp_type;
              tmp_type=entry.subtype;
              designator.push_entry(entry);
              found=repeat=true;
              break;
            }

            ++number;
          }
        }
        while(repeat);

        if(!found)
        {
          error().source_location = d_op.source_location();
          error() << "failed to find struct component '" << component_name
                  << "' in initialization of '" << to_string(struct_union_type)
                  << "'" << eom;
          throw 0;
        }
      }
    }
    else
    {
      error().source_location = d_op.source_location();
      error() << "designated initializers cannot initialize '"
              << to_string(full_type) << "'" << eom;
      throw 0;
    }

    type=entry.subtype;
    designator.push_entry(entry);
  }

  assert(!designator.empty());

  return designator;
}

exprt c_typecheck_baset::do_initializer_list(
  const exprt &value,
  const typet &type,
  bool force_constant)
{
  assert(value.id()==ID_initializer_list);

  const typet &full_type=follow(type);

  // 6.7.9, 14: An array of character type may be initialized by a character
  // string literal or UTF-8 string literal, optionally enclosed in braces.
  if(
    full_type.id() == ID_array && value.operands().size() >= 1 &&
    to_multi_ary_expr(value).op0().id() == ID_string_constant &&
    (to_array_type(full_type).element_type().id() == ID_signedbv ||
     to_array_type(full_type).element_type().id() == ID_unsignedbv) &&
    to_bitvector_type(to_array_type(full_type).element_type()).get_width() ==
      char_type().get_width())
  {
    if(value.operands().size() > 1)
    {
      warning().source_location = value.find_source_location();
      warning() << "ignoring excess initializers" << eom;
    }

    return do_initializer_rec(
      to_multi_ary_expr(value).op0(), type, force_constant);
  }

  exprt result;
  if(full_type.id()==ID_struct ||
     full_type.id()==ID_union ||
     full_type.id()==ID_vector)
  {
    // start with zero everywhere
    const auto zero = zero_initializer(type, value.source_location(), *this);
    if(!zero.has_value())
    {
      error().source_location = value.source_location();
      error() << "cannot zero-initialize '" << to_string(full_type) << "'"
              << eom;
      throw 0;
    }
    result = *zero;
  }
  else if(full_type.id()==ID_array)
  {
    if(to_array_type(full_type).size().is_nil())
    {
      // start with empty array
      result = array_exprt({}, to_array_type(full_type));
      result.add_source_location()=value.source_location();
    }
    else
    {
      // start with zero everywhere
      const auto zero = zero_initializer(type, value.source_location(), *this);
      if(!zero.has_value())
      {
        error().source_location = value.source_location();
        error() << "cannot zero-initialize '" << to_string(full_type) << "'"
                << eom;
        throw 0;
      }
      result = *zero;
    }
  }
  else
  {
    // The initializer for a scalar shall be a single expression,
    // * optionally enclosed in braces. *

    if(value.operands().size()==1)
      return do_initializer_rec(
        to_unary_expr(value).op(), type, force_constant);

    error().source_location = value.source_location();
    error() << "cannot initialize '" << to_string(full_type)
            << "' with an initializer list" << eom;
    throw 0;
  }

  designatort current_designator;

  designator_enter(type, current_designator);

  const exprt::operandst &operands=value.operands();
  for(exprt::operandst::const_iterator it=operands.begin();
      it!=operands.end(); ) // no ++it
  {
    it=do_designated_initializer(
      result, current_designator, value, it, force_constant);

    // increase designator -- might go up
    increment_designator(current_designator);
  }

  if(full_type.id()==ID_struct)
  {
    const struct_typet &full_struct_type = to_struct_type(full_type);
    const struct_typet::componentst &components = full_struct_type.components();
    // make sure we didn't mess up index computation
    CHECK_RETURN(result.operands().size() == components.size());

    if(
      !components.empty() &&
      components.back().type().get_bool(ID_C_flexible_array_member))
    {
      const auto array_size = numeric_cast<mp_integer>(
        to_array_type(components.back().type()).size());
      array_exprt &init_array = to_array_expr(result.operands().back());
      if(
        !array_size.has_value() ||
        (*array_size <= 1 && init_array.operands().size() != *array_size))
      {
        struct_typet actual_struct_type = full_struct_type;
        array_typet &actual_array_type =
          to_array_type(actual_struct_type.components().back().type());
        actual_array_type.size() = from_integer(
          init_array.operands().size(), actual_array_type.index_type());
        actual_array_type.set(ID_C_flexible_array_member, true);
        init_array.type() = actual_array_type;

        // mimic bits of typecheck_compound_type to produce a new struct tag
        actual_struct_type.remove(ID_tag);
        type_symbolt compound_symbol{actual_struct_type};
        compound_symbol.mode = mode;
        compound_symbol.location = value.source_location();
        std::string typestr = type2name(compound_symbol.type, *this);
        compound_symbol.base_name = "#anon#" + typestr;
        compound_symbol.name = "tag-#anon#" + typestr;
        irep_idt tag_identifier = compound_symbol.name;

        // We might already have the same anonymous struct, which is fine as it
        // will be exactly the same type.
        symbol_table.insert(std::move(compound_symbol));

        result.type() = struct_tag_typet{tag_identifier};
      }
    }
  }

  if(full_type.id()==ID_array &&
     to_array_type(full_type).size().is_nil())
  {
    // make complete by setting array size
    array_typet &array_type = to_array_type(result.type());
    array_type.size() =
      from_integer(result.operands().size(), array_type.index_type());
  }

  return result;
}
