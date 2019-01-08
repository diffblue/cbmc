/*******************************************************************\

Module: ANSI-C Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Conversion / Type Checking

#include "c_typecheck_base.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_initializer.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>
#include <util/type_eq.h>

#include "anonymous_member.h"

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
    if(result.id()!=ID_array)
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
    error() << "type `" << to_string(type)
            << "' is still incomplete -- cannot initialize" << eom;
    throw 0;
  }

  if(value.id()==ID_initializer_list)
    return do_initializer_list(value, type, force_constant);

  if(
    value.id() == ID_array && value.get_bool(ID_C_string_constant) &&
    full_type.id() == ID_array &&
    (full_type.subtype().id() == ID_signedbv ||
     full_type.subtype().id() == ID_unsignedbv) &&
    to_bitvector_type(full_type.subtype()).get_width() ==
      to_bitvector_type(value.type().subtype()).get_width())
  {
    exprt tmp=value;

    // adjust char type
    tmp.type().subtype()=full_type.subtype();

    Forall_operands(it, tmp)
      it->type()=full_type.subtype();

    if(full_type.id()==ID_array &&
       to_array_type(full_type).is_complete())
    {
      // check size
      mp_integer array_size;
      if(to_integer(to_array_type(full_type).size(), array_size))
      {
        error().source_location = value.source_location();
        error() << "array size needs to be constant, got "
                << to_string(to_array_type(full_type).size()) << eom;
        throw 0;
      }

      if(array_size<0)
      {
        error().source_location = value.source_location();
        error() << "array size must not be negative" << eom;
        throw 0;
      }

      if(mp_integer(tmp.operands().size())>array_size)
      {
        // cut off long strings. gcc does a warning for this
        tmp.operands().resize(numeric_cast_v<std::size_t>(array_size));
        tmp.type()=type;
      }
      else if(mp_integer(tmp.operands().size())<array_size)
      {
        // fill up
        tmp.type()=type;
        const auto zero =
          zero_initializer(full_type.subtype(), value.source_location(), *this);
        if(!zero.has_value())
        {
          error().source_location = value.source_location();
          error() << "cannot zero-initialize array with subtype `"
                  << to_string(full_type.subtype()) << "'" << eom;
          throw 0;
        }
        tmp.operands().resize(numeric_cast_v<std::size_t>(array_size), *zero);
      }
    }

    return tmp;
  }

  if(
    value.id() == ID_string_constant && full_type.id() == ID_array &&
    (full_type.subtype().id() == ID_signedbv ||
     full_type.subtype().id() == ID_unsignedbv) &&
    to_bitvector_type(full_type.subtype()).get_width() ==
      char_type().get_width())
  {
    // will go away, to be replaced by the above block

    string_constantt tmp1=to_string_constant(value);
    // adjust char type
    tmp1.type().subtype()=full_type.subtype();

    exprt tmp2=tmp1.to_array_expr();

    if(full_type.id()==ID_array &&
       to_array_type(full_type).is_complete())
    {
      // check size
      mp_integer array_size;
      if(to_integer(to_array_type(full_type).size(), array_size))
      {
        error().source_location = value.source_location();
        error() << "array size needs to be constant, got "
                << to_string(to_array_type(full_type).size()) << eom;
        throw 0;
      }

      if(array_size<0)
      {
        error().source_location = value.source_location();
        error() << "array size must not be negative" << eom;
        throw 0;
      }

      if(mp_integer(tmp2.operands().size())>array_size)
      {
        // cut off long strings. gcc does a warning for this
        tmp2.operands().resize(numeric_cast_v<std::size_t>(array_size));
        tmp2.type()=type;
      }
      else if(mp_integer(tmp2.operands().size())<array_size)
      {
        // fill up
        tmp2.type()=type;
        const auto zero =
          zero_initializer(full_type.subtype(), value.source_location(), *this);
        if(!zero.has_value())
        {
          error().source_location = value.source_location();
          error() << "cannot zero-initialize array with subtype `"
                  << to_string(full_type.subtype()) << "'" << eom;
          throw 0;
        }
        tmp2.operands().resize(numeric_cast_v<std::size_t>(array_size), *zero);
      }
    }

    return tmp2;
  }

  if(full_type.id()==ID_array &&
     to_array_type(full_type).size().is_nil())
  {
    error().source_location = value.source_location();
    error() << "type `" << to_string(full_type)
            << "' cannot be initialized with `" << to_string(value)
            << "'" << eom;
    throw 0;
  }

  if(value.id()==ID_designated_initializer)
  {
    error().source_location = value.source_location();
    error() << "type `" << to_string(full_type)
            << "' cannot be initialized with designated initializer"
            << eom;
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

  if(symbol.is_static_lifetime)
  {
    if(symbol.value.is_not_nil())
    {
      typecheck_expr(symbol.value);
      do_initializer(symbol.value, symbol.type, true);

      // need to adjust size?
      if(
        symbol.type.id() == ID_array &&
        to_array_type(symbol.type).size().is_nil())
        symbol.type=symbol.value.type();
    }
  }
  else if(!symbol.is_type)
  {
    if(symbol.is_macro)
    {
      // these must have a constant value
      assert(symbol.value.is_not_nil());
      typecheck_expr(symbol.value);
      source_locationt location=symbol.value.source_location();
      do_initializer(symbol.value, symbol.type, true);
      make_constant(symbol.value);
    }
    else if(symbol.value.is_not_nil())
    {
      typecheck_expr(symbol.value);
      do_initializer(symbol.value, symbol.type, true);

      // need to adjust size?
      if(
        symbol.type.id() == ID_array &&
        to_array_type(symbol.type).size().is_nil())
        symbol.type=symbol.value.type();
    }
  }
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
      entry.subtype=array_type.subtype();
    }
    else
    {
      mp_integer array_size;

      if(to_integer(array_type.size(), array_size))
      {
        error().source_location = array_type.size().source_location();
        error() << "array has non-constant size `"
                << to_string(array_type.size()) << "'" << eom;
        throw 0;
      }

      entry.size = numeric_cast_v<std::size_t>(array_size);
      entry.subtype=array_type.subtype();
    }
  }
  else if(full_type.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(full_type);

    mp_integer vector_size;

    if(to_integer(vector_type.size(), vector_size))
    {
      error().source_location = vector_type.size().source_location();
      error() << "vector has non-constant size `"
              << to_string(vector_type.size()) << "'" << eom;
      throw 0;
    }

    entry.size = numeric_cast_v<std::size_t>(vector_size);
    entry.subtype=vector_type.subtype();
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
      if(index>=dest->operands().size())
      {
        if(full_type.id()==ID_array &&
           (to_array_type(full_type).size().is_zero() ||
            to_array_type(full_type).size().is_nil()))
        {
          // we are willing to grow an incomplete or zero-sized array
          const auto zero = zero_initializer(
            full_type.subtype(), value.source_location(), *this);
          if(!zero.has_value())
          {
            error().source_location = value.source_location();
            error() << "cannot zero-initialize array with subtype `"
                    << to_string(full_type.subtype()) << "'" << eom;
            throw 0;
          }
          dest->operands().resize(
            numeric_cast_v<std::size_t>(index) + 1, *zero);

          // todo: adjust type!
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

      DATA_INVARIANT(index<components.size(),
                     "member designator is bounded by components size");

      const union_typet::componentt &component=union_type.components()[index];

      if(dest->id()==ID_union &&
         dest->get(ID_component_name)==component.get_name())
      {
        // Already right union component. We can initialize multiple submembers,
        // so do not overwrite this.
      }
      else
      {
        // Note that gcc issues a warning if the union component is switched.
        // Build a union expression from given component.
        const auto zero =
          zero_initializer(component.type(), value.source_location(), *this);
        if(!zero.has_value())
        {
          error().source_location = value.source_location();
          error() << "cannot zero-initialize union component of type `"
                  << to_string(component.type()) << "'" << eom;
          throw 0;
        }
        union_exprt union_expr(component.get_name(), *zero, type);
        union_expr.add_source_location()=value.source_location();
        *dest=union_expr;
      }

      dest=&(dest->op0());
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
    CHECK_RETURN(full_type.id() != ID_symbol_type);

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
        *dest=do_initializer_rec(value.op0(), type, force_constant);
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
          error() << "cannot zero-initialize union component of type `"
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
        (full_type.subtype().id() == ID_signedbv ||
         full_type.subtype().id() == ID_unsignedbv))
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
        error() << "cannot initialize type `"
          << to_string(dest_type) << "' using value `"
          << to_string(value) << "'" << eom;
        throw 0;
      }
    }

    dest=&(dest->op0());

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

      assert(d_op.operands().size()==1);
      exprt tmp_index=d_op.op0();
      make_constant_index(tmp_index);

      mp_integer index, size;

      if(to_integer(tmp_index, index))
      {
        error().source_location = d_op.op0().source_location();
        error() << "expected constant array index designator" << eom;
        throw 0;
      }

      if(to_array_type(full_type).size().is_nil())
        size=0;
      else if(to_integer(to_array_type(full_type).size(), size))
      {
        error().source_location = d_op.op0().source_location();
        error() << "expected constant array size" << eom;
        throw 0;
      }

      entry.index = numeric_cast_v<std::size_t>(index);
      entry.size = numeric_cast_v<std::size_t>(size);
      entry.subtype=full_type.subtype();
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
              c.get_anonymous() && (follow(c.type()).id() == ID_struct ||
                                    follow(c.type()).id() == ID_union) &&
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
          error() << "failed to find struct component `"
                  << component_name << "' in initialization of `"
                  << to_string(struct_union_type) << "'" << eom;
          throw 0;
        }
      }
    }
    else
    {
      error().source_location = d_op.source_location();
      error() << "designated initializers cannot initialize `"
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
      error() << "cannot zero-initialize `" << to_string(full_type) << "'"
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
      result=exprt(ID_array, full_type);
      result.add_source_location()=value.source_location();
    }
    else
    {
      // start with zero everywhere
      const auto zero = zero_initializer(type, value.source_location(), *this);
      if(!zero.has_value())
      {
        error().source_location = value.source_location();
        error() << "cannot zero-initialize `" << to_string(full_type) << "'"
                << eom;
        throw 0;
      }
      result = *zero;
    }

    // 6.7.9, 14: An array of character type may be initialized by a character
    // string literal or UTF-8 string literal, optionally enclosed in braces.
    if(
      value.operands().size() >= 1 && value.op0().id() == ID_string_constant &&
      (full_type.subtype().id() == ID_signedbv ||
       full_type.subtype().id() == ID_unsignedbv) &&
      to_bitvector_type(full_type.subtype()).get_width() ==
        char_type().get_width())
    {
      if(value.operands().size()>1)
      {
        warning().source_location=value.find_source_location();
        warning() << "ignoring excess initializers" << eom;
      }

      return do_initializer_rec(value.op0(), type, force_constant);
    }
  }
  else
  {
    // The initializer for a scalar shall be a single expression,
    // * optionally enclosed in braces. *

    if(value.operands().size()==1)
      return do_initializer_rec(value.op0(), type, force_constant);

    error().source_location = value.source_location();
    error() << "cannot initialize `" << to_string(full_type)
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

  // make sure we didn't mess up index computation
  if(full_type.id()==ID_struct)
  {
    assert(result.operands().size()==
           to_struct_type(full_type).components().size());
  }

  if(full_type.id()==ID_array &&
     to_array_type(full_type).size().is_nil())
  {
    // make complete by setting array size
    size_t size=result.operands().size();
    result.type().id(ID_array);
    result.type().set(ID_size, from_integer(size, index_type()));
  }

  return result;
}
