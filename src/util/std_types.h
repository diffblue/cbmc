/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STD_TYPES_H
#define CPROVER_STD_TYPES_H

/*! \file util/std_types.h
 * \brief API to type classes
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

#include <cassert>

#include "expr.h"
#include "mp_arith.h"

class constant_exprt;

/*! \defgroup gr_std_types Conversion to specific types
 *  Conversion to subclasses of @ref typet
*/

/*! \brief The proper Booleans
*/
class bool_typet:public typet
{
public:
  inline bool_typet():typet(ID_bool)
  {
  }
};

/*! \brief The NIL type
*/
class nil_typet:public typet
{
public:
  inline nil_typet():typet(static_cast<const typet &>(get_nil_irep()))
  {
  }
};

/*! \brief The empty type
*/
class empty_typet:public typet
{
public:
  inline empty_typet():typet(ID_empty)
  {
  }
};

/*! \brief The void type
*/
class void_typet:public empty_typet
{
};

/*! \brief Unbounded, signed integers
*/
class integer_typet:public typet
{
public:
  inline integer_typet():typet(ID_integer)
  {
  }
};

/*! \brief Natural numbers (which include zero)
*/
class natural_typet:public typet
{
public:
  inline natural_typet():typet(ID_natural)
  {
  }
};

/*! \brief Unbounded, signed rational numbers
*/
class rational_typet:public typet
{
public:
  inline rational_typet():typet(ID_rational)
  {
  }
};

/*! \brief Unbounded, signed real numbers
*/
class real_typet:public typet
{
public:
  inline real_typet():typet(ID_real)
  {
  }
};

/*! \brief A reference into the symbol table
*/
class symbol_typet:public typet
{
public:
  inline symbol_typet():typet(ID_symbol)
  {
  }
  
  inline explicit symbol_typet(const irep_idt &identifier):typet(ID_symbol)
  {
    set_identifier(identifier);
  }

  inline void set_identifier(const irep_idt &identifier)
  {
    set(ID_identifier, identifier);
  }

  inline const irep_idt &get_identifier() const
  {
    return get(ID_identifier);
  }  
};

/*! \brief Cast a generic typet to a \ref symbol_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * symbol_typet.
 *
 * \param type Source type
 * \return Object of type \ref symbol_typet
 *
 * \ingroup gr_std_types
*/
extern inline const symbol_typet &to_symbol_type(const typet &type)
{
  assert(type.id()==ID_symbol);
  return static_cast<const symbol_typet &>(type);
}

/*! \copydoc to_symbol_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline symbol_typet &to_symbol_type(typet &type)
{
  assert(type.id()==ID_symbol);
  return static_cast<symbol_typet &>(type);
}

/*! \brief Base type of C structs and unions, and C++ classes
*/
class struct_union_typet:public typet
{
public:
  inline explicit struct_union_typet(const irep_idt &_id):typet(_id)
  {
  }

  class componentt:public exprt
  {
  public:
    inline componentt()
    {
    }
  
    inline componentt(const irep_idt &_name, const typet &_type)
    {
      set_name(_name);
      type()=_type;
    }
  
    inline const irep_idt &get_name() const
    {
      return get(ID_name);
    }

    inline void set_name(const irep_idt &name)
    {
      return set(ID_name, name);
    }

    inline const irep_idt &get_base_name() const
    {
      return get(ID_base_name);
    }

    inline void set_base_name(const irep_idt &base_name)
    {
      return set(ID_base_name, base_name);
    }

    inline const irep_idt &get_access() const
    {
      return get(ID_access);
    }

    inline void set_access(const irep_idt &access)
    {
      return set(ID_access, access);
    }

    inline const irep_idt &get_pretty_name() const
    {
      return get(ID_pretty_name);
    }

    inline void set_pretty_name(const irep_idt &name)
    {
      return set(ID_pretty_name, name);
    }

    inline const bool get_anonymous() const
    {
      return get_bool(ID_anonymous);
    }

    inline void set_anonymous(bool anonymous)
    {
      return set(ID_anonymous, anonymous);
    }

    inline const bool get_is_padding() const
    {
      return get_bool(ID_C_is_padding);
    }

    inline void set_is_padding(bool is_padding)
    {
      return set(ID_C_is_padding, is_padding);
    }
  };

  typedef std::vector<componentt> componentst;
  
  inline const componentst &components() const
  {
    return (const componentst &)(find(ID_components).get_sub());
  }
  
  inline componentst &components()
  {
    return (componentst &)(add(ID_components).get_sub());
  }
  
  inline bool has_component(const irep_idt &component_name) const
  {
    return get_component(component_name).is_not_nil();
  }
  
  const componentt &get_component(
    const irep_idt &component_name) const;

  unsigned component_number(const irep_idt &component_name) const;
  typet component_type(const irep_idt &component_name) const;
  
  irep_idt get_tag() const { return get(ID_tag); }
  void set_tag(const irep_idt &tag) { set(ID_tag, tag); }
};

/*! \brief Cast a generic typet to a \ref struct_union_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * struct_union_typet.
 *
 * \param type Source type
 * \return Object of type \ref struct_union_typet
 *
 * \ingroup gr_std_types
*/
extern inline const struct_union_typet &to_struct_union_type(const typet &type)
{
  assert(type.id()==ID_struct ||
         type.id()==ID_union);
  return static_cast<const struct_union_typet &>(type);
}

/*! \copydoc to_struct_union_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline struct_union_typet &to_struct_union_type(typet &type)
{
  assert(type.id()==ID_struct ||
         type.id()==ID_union);
  return static_cast<struct_union_typet &>(type);
}

/*! \brief Structure type
*/
class struct_typet:public struct_union_typet
{
public:
  inline struct_typet():struct_union_typet(ID_struct)
  {
  }

  // returns true if the object is a prefix of \a other    
  bool is_prefix_of(const struct_typet &other) const;
};

/*! \brief Cast a generic typet to a \ref struct_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * struct_typet.
 *
 * \param type Source type
 * \return Object of type \ref struct_typet
 *
 * \ingroup gr_std_types
*/
extern inline const struct_typet &to_struct_type(const typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<const struct_typet &>(type);
}

/*! \copydoc to_struct_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline struct_typet &to_struct_type(typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<struct_typet &>(type);
}

/*! \brief C++ class type
*/
class class_typet:public struct_typet
{
public:
  inline class_typet():struct_typet()
  {
    set(ID_C_class, true);
  }
  
  typedef componentt methodt;
  typedef componentst methodst;

  inline const methodst &methods() const
  {
    return (const methodst &)(find(ID_methods).get_sub());
  }
  
  inline componentst &methods()
  {
    return (methodst &)(add(ID_methods).get_sub());
  }

  inline bool is_class() const
  {
    return get_bool(ID_C_class);
  }
  
  inline irep_idt default_access() const
  {
    return is_class()?ID_private:ID_public;
  }

  inline const irept::subt &bases() const  
  {
    return find(ID_bases).get_sub();
  }
  
  inline irept::subt &bases()
  {
    return add(ID_bases).get_sub();
  }
  
  inline void add_base(const typet &base)
  {
    bases().push_back(exprt(ID_base, base));
  }
  
  bool has_base(const irep_idt &id) const
  {
    const irept::subt &b=bases();

    forall_irep(it, b)
    {
      assert(it->id()==ID_base);
      const irept &type=it->find(ID_type);
      assert(type.id()==ID_symbol);
      if(type.get(ID_identifier)==id) return true;
    }
    
    return false;
  }

};

/*! \brief Cast a generic typet to a \ref class_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * class_typet.
 *
 * \param type Source type
 * \return Object of type \ref class_typet
 *
 * \ingroup gr_std_types
*/
extern inline const class_typet &to_class_type(const typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<const class_typet &>(type);
}

/*! \copydoc to_class_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline class_typet &to_class_type(typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<class_typet &>(type);
}

/*! \brief The union type
*/
class union_typet:public struct_union_typet
{
public:
  inline union_typet():struct_union_typet(ID_union)
  {
  }
};

/*! \brief Cast a generic typet to a \ref union_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * union_typet.
 *
 * \param type Source type
 * \return Object of type \ref union_typet
 *
 * \ingroup gr_std_types
*/
extern inline const union_typet &to_union_type(const typet &type)
{
  assert(type.id()==ID_union);
  return static_cast<const union_typet &>(type);
}

/*! \copydoc to_union_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline union_typet &to_union_type(typet &type)
{
  assert(type.id()==ID_union);
  return static_cast<union_typet &>(type);
}

/*! \brief A generic tag-based type
*/

class tag_typet:public typet
{
public:
  inline explicit tag_typet(const irep_idt &_id):typet(_id)
  {
  }

  inline explicit tag_typet(
    const irep_idt &_id,
    const irep_idt &identifier):typet(_id)
  {
    set_identifier(identifier);
  }

  inline void set_identifier(const irep_idt &identifier)
  {
    set(ID_identifier, identifier);
  }

  inline const irep_idt &get_identifier() const
  {
    return get(ID_identifier);
  }  
};

/*! \brief A struct tag type
*/

class struct_tag_typet:public tag_typet
{
public:
  explicit inline struct_tag_typet(const irep_idt &identifier):
    tag_typet(ID_struct_tag, identifier)
  {
  }
};

/*! \brief Cast a generic typet to a \ref union_tag_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * union_tag_typet.
 *
 * \param type Source type
 * \return Object of type \ref union_tag_typet
 *
 * \ingroup gr_std_types
*/
extern inline const struct_tag_typet &to_struct_tag_type(const typet &type)
{
  assert(type.id()==ID_struct_tag);
  return static_cast<const struct_tag_typet &>(type);
}

/*! \copydoc to_struct_tag_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline struct_tag_typet &to_struct_tag_type(typet &type)
{
  assert(type.id()==ID_struct_tag);
  return static_cast<struct_tag_typet &>(type);
}

/*! \brief A union tag type
*/

class union_tag_typet:public tag_typet
{
public:
  explicit inline union_tag_typet(const irep_idt &identifier):
    tag_typet(ID_union_tag, identifier)
  {
  }
};

/*! \brief Cast a generic typet to a \ref union_tag_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * union_tag_typet.
 *
 * \param type Source type
 * \return Object of type \ref union_tag_typet
 *
 * \ingroup gr_std_types
*/
extern inline const union_tag_typet &to_union_tag_type(const typet &type)
{
  assert(type.id()==ID_union_tag);
  return static_cast<const union_tag_typet &>(type);
}

/*! \copydoc to_union_tag_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline union_tag_typet &to_union_tag_type(typet &type)
{
  assert(type.id()==ID_union_tag);
  return static_cast<union_tag_typet &>(type);
}

/*! \brief The type of C enums
*/

class c_enum_typet:public type_with_subtypet
{
public:
  explicit c_enum_typet(const typet &_subtype):type_with_subtypet(ID_c_enum, _subtype)
  {
  }
  
  class c_enum_membert:public irept
  {
  public:
    inline irep_idt get_value() const { return get(ID_value); }
    inline void set_value(const irep_idt &value) { set(ID_value, value); }
    inline irep_idt get_identifier() const { return get(ID_identifier); }
    inline void set_identifier(const irep_idt &identifier) { set(ID_identifier, identifier); }
    inline irep_idt get_base_name() const { return get(ID_base_name); }    
    inline void set_base_name(const irep_idt &base_name) { set(ID_base_name, base_name); }
  };
  
  typedef std::vector<c_enum_membert> memberst;

  inline const memberst &members() const
  {
    return (const memberst &)(find(ID_body).get_sub());
  }
};

/*! \brief Cast a generic typet to a \ref c_enum_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * c_enum_typet.
 *
 * \param type Source type
 * \return Object of type \ref c_enum_typet
 *
 * \ingroup gr_std_types
*/
extern inline const c_enum_typet &to_c_enum_type(const typet &type)
{
  assert(type.id()==ID_c_enum);
  return static_cast<const c_enum_typet &>(type);
}

/*! \copydoc to_c_enum_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline c_enum_typet &to_c_enum_type(typet &type)
{
  assert(type.id()==ID_c_enum);
  return static_cast<c_enum_typet &>(type);
}

/*! \brief An enum tag type
*/

class c_enum_tag_typet:public tag_typet
{
public:
  explicit inline c_enum_tag_typet(const irep_idt &identifier):
    tag_typet(ID_c_enum_tag, identifier)
  {
  }
};

/*! \brief Cast a generic typet to a \ref c_enum_tag_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * c_enum_tag_typet.
 *
 * \param type Source type
 * \return Object of type \ref c_enum_tag_typet
 *
 * \ingroup gr_std_types
*/
extern inline const c_enum_tag_typet &to_c_enum_tag_type(const typet &type)
{
  assert(type.id()==ID_c_enum_tag);
  return static_cast<const c_enum_tag_typet &>(type);
}

/*! \copydoc to_enum_tag_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline c_enum_tag_typet &to_c_enum_tag_type(typet &type)
{
  assert(type.id()==ID_c_enum_tag);
  return static_cast<c_enum_tag_typet &>(type);
}

/*! \brief Base type of functions
*/
class code_typet:public typet
{
public:
  inline code_typet():typet(ID_code)
  {
  }
  
  // used to be argumentt -- now uses standard terminology

  class parametert:public exprt
  {
  public:
    inline parametert():exprt(ID_parameter)
    {
    }
    
    explicit inline parametert(const typet &type):exprt(ID_parameter, type)
    {
    }
    
    inline const exprt &default_value() const
    {
      return find_expr(ID_C_default_value);
    }

    inline bool has_default_value() const
    {
      return default_value().is_not_nil();
    }

    inline exprt &default_value()
    {
      return add_expr(ID_C_default_value);
    }
    
    // The following for methods will go away;
    // these should not be part of the signature of a function,
    // but rather part of the body.
    inline void set_identifier(const irep_idt &identifier)
    {
      set(ID_C_identifier, identifier);
    }

    inline void set_base_name(const irep_idt &name)
    {
      set(ID_C_base_name, name);
    }

    inline const irep_idt &get_identifier() const
    {
      return get(ID_C_identifier);
    }

    inline const irep_idt &get_base_name() const
    {
      return get(ID_C_base_name);
    }
  };
  
  inline bool has_ellipsis() const
  {
    return find(ID_parameters).get_bool(ID_ellipsis);
  }

  inline bool is_KnR() const
  {
    return get_bool(ID_C_KnR);
  }

  inline void make_ellipsis()
  {
    add(ID_parameters).set(ID_ellipsis, true);
  }

  inline void remove_ellipsis()
  {
    add(ID_parameters).remove(ID_ellipsis);
  }

  typedef std::vector<parametert> parameterst;

  inline const typet &return_type() const
  {
    return find_type(ID_return_type);
  }

  inline typet &return_type()
  {
    return add_type(ID_return_type);
  }
  
  inline const parameterst &parameters() const
  {
    return (const parameterst &)find(ID_parameters).get_sub();
  }

  inline parameterst &parameters()
  {
    return (parameterst &)add(ID_parameters).get_sub();
  }
  
  inline bool get_inlined() const
  {
    return get_bool(ID_C_inlined);
  }

  inline void set_inlined(bool value)
  {
    set(ID_C_inlined, value);
  }
  
  // this produces the list of parameter identifiers
  std::vector<irep_idt> parameter_identifiers() const
  {
    std::vector<irep_idt> result;
    const parameterst &p=parameters();
    result.reserve(p.size());
    for(parameterst::const_iterator it=p.begin();
        it!=p.end(); it++)
      result.push_back(it->get_identifier());
    return result;
  }
};

/*! \brief Cast a generic typet to a \ref code_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * code_typet.
 *
 * \param type Source type
 * \return Object of type \ref code_typet
 *
 * \ingroup gr_std_types
*/
extern inline const code_typet &to_code_type(const typet &type)
{
  assert(type.id()==ID_code);
  return static_cast<const code_typet &>(type);
}

/*! \copydoc to_code_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline code_typet &to_code_type(typet &type)
{
  assert(type.id()==ID_code);
  return static_cast<code_typet &>(type);
}

/*! \brief arrays with given size
*/
class array_typet:public type_with_subtypet
{
public:
  inline array_typet():type_with_subtypet(ID_array)
  {
  }
  
  inline array_typet(const typet &_subtype,
                     const exprt &_size):type_with_subtypet(ID_array, _subtype)
  {
    size()=_size;
  }
  
  inline const exprt &size() const
  {
    return static_cast<const exprt &>(find(ID_size));
  }
  
  inline exprt &size()
  {
    return static_cast<exprt &>(add(ID_size));
  }
  
  inline bool is_complete() const
  {
    return size().is_not_nil();
  }

  inline bool is_incomplete() const
  {
    return size().is_nil();
  }

};

/*! \brief Cast a generic typet to an \ref array_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * array_typet.
 *
 * \param type Source type
 * \return Object of type \ref array_typet
 *
 * \ingroup gr_std_types
*/
extern inline const array_typet &to_array_type(const typet &type)
{
  assert(type.id()==ID_array);
  return static_cast<const array_typet &>(type);
}

/*! \copydoc to_array_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline array_typet &to_array_type(typet &type)
{
  assert(type.id()==ID_array);
  return static_cast<array_typet &>(type);
}

/*! \brief arrays without size
*/
class incomplete_array_typet:public type_with_subtypet
{
public:
  inline incomplete_array_typet():type_with_subtypet(ID_incomplete_array)
  {
  }
  
  inline incomplete_array_typet(const typet &_subtype):
    type_with_subtypet(ID_array, _subtype)
  {
  }
};

/*! \brief Cast a generic typet to an \ref incomplete_array_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * incomplete_array_typet.
 *
 * \param type Source type
 * \return Object of type \ref incomplete_array_typet
 *
 * \ingroup gr_std_types
*/
extern inline const incomplete_array_typet &to_incomplete_array_type(const typet &type)
{
  assert(type.id()==ID_array);
  return static_cast<const incomplete_array_typet &>(type);
}

/*! \copydoc to_incomplete_array_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline incomplete_array_typet &to_incomplete_array_type(typet &type)
{
  assert(type.id()==ID_array);
  return static_cast<incomplete_array_typet &>(type);
}

/*! \brief Base class of bitvector types
*/
class bitvector_typet:public type_with_subtypet
{
public:
  inline explicit bitvector_typet(const irep_idt &_id):type_with_subtypet(_id)
  {
  }

  inline bitvector_typet(const irep_idt &_id, const typet &_subtype):
    type_with_subtypet(_id, _subtype)
  {
  }

  inline bitvector_typet(const irep_idt &_id, const typet &_subtype, unsigned width):
    type_with_subtypet(_id, _subtype)
  {
    set_width(width);
  }

  inline bitvector_typet(const irep_idt &_id, unsigned width):
    type_with_subtypet(_id)
  {
    set_width(width);
  }

  inline unsigned get_width() const
  {
    return get_unsigned_int(ID_width);
  }

  inline void set_width(unsigned width)
  {
    set(ID_width, width);
  }
};

/*! \brief Cast a generic typet to a \ref bitvector_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * bitvector_typet.
 *
 * \param type Source type
 * \return Object of type \ref bitvector_typet
 *
 * \ingroup gr_std_types
*/
inline const bitvector_typet &to_bitvector_type(const typet &type)
{
  assert(type.id()==ID_signedbv ||
         type.id()==ID_unsignedbv ||
         type.id()==ID_fixedbv ||
         type.id()==ID_floatbv ||
         type.id()==ID_verilogbv ||
         type.id()==ID_bv ||
         type.id()==ID_pointer ||
         type.id()==ID_c_bit_field ||
         type.id()==ID_c_bool);

  return static_cast<const bitvector_typet &>(type);
}

/*! \brief fixed-width bit-vector without numerical interpretation
*/
class bv_typet:public bitvector_typet
{
public:
  inline bv_typet():bitvector_typet(ID_bv)
  {
  }

  inline explicit bv_typet(unsigned width):bitvector_typet(ID_bv)
  {
    set_width(width);
  }
};

/*! \brief Cast a generic typet to a \ref bv_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * bv_typet.
 *
 * \param type Source type
 * \return Object of type \ref bv_typet
 *
 * \ingroup gr_std_types
*/
inline const bv_typet &to_bv_type(const typet &type)
{
  assert(type.id()==ID_bv);
  return static_cast<const bv_typet &>(type);
}

/*! \copydoc to_bv_type(const typet &)
 * \ingroup gr_std_types
*/
inline bv_typet &to_bv_type(typet &type)
{
  assert(type.id()==ID_bv);
  return static_cast<bv_typet &>(type);
}

/*! \brief Fixed-width bit-vector with unsigned binary interpretation
*/
class unsignedbv_typet:public bitvector_typet
{
public:
  inline unsignedbv_typet():bitvector_typet(ID_unsignedbv)
  {
  }

  inline explicit unsignedbv_typet(unsigned width):bitvector_typet(ID_unsignedbv, width)
  {
  }
  
  mp_integer smallest() const;
  mp_integer largest() const;
  constant_exprt smallest_expr() const;
  constant_exprt zero_expr() const;
  constant_exprt largest_expr() const;
};

/*! \brief Cast a generic typet to an \ref unsignedbv_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * unsignedbv_typet.
 *
 * \param type Source type
 * \return Object of type \ref unsignedbv_typet
 *
 * \ingroup gr_std_types
*/
inline const unsignedbv_typet &to_unsignedbv_type(const typet &type)
{
  assert(type.id()==ID_unsignedbv);
  return static_cast<const unsignedbv_typet &>(type);
}

/*! \copydoc to_unsignedbv_type(const typet &)
 * \ingroup gr_std_types
*/
inline unsignedbv_typet &to_unsignedbv_type(typet &type)
{
  assert(type.id()==ID_unsignedbv);
  return static_cast<unsignedbv_typet &>(type);
}

/*! \brief Fixed-width bit-vector with two's complement interpretation
*/
class signedbv_typet:public bitvector_typet
{
public:
  inline signedbv_typet():bitvector_typet(ID_signedbv)
  {
  }

  inline explicit signedbv_typet(unsigned width):bitvector_typet(ID_signedbv, width)
  {
  }

  mp_integer smallest() const;
  mp_integer largest() const;
  constant_exprt smallest_expr() const;
  constant_exprt zero_expr() const;
  constant_exprt largest_expr() const;
};

/*! \brief Cast a generic typet to a \ref signedbv_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * signedbv_typet.
 *
 * \param type Source type
 * \return Object of type \ref signedbv_typet
 *
 * \ingroup gr_std_types
*/
inline const signedbv_typet &to_signedbv_type(const typet &type)
{
  assert(type.id()==ID_signedbv);
  return static_cast<const signedbv_typet &>(type);
}

/*! \copydoc to_signedbv_type(const typet &)
 * \ingroup gr_std_types
*/
inline signedbv_typet &to_signedbv_type(typet &type)
{
  assert(type.id()==ID_signedbv);
  return static_cast<signedbv_typet &>(type);
}

/*! \brief Fixed-width bit-vector with signed fixed-point interpretation
*/
class fixedbv_typet:public bitvector_typet
{
public:
  inline fixedbv_typet():bitvector_typet(ID_fixedbv)
  {
  }

  inline unsigned get_fraction_bits() const
  {
    return get_width()-get_integer_bits();
  }

  unsigned get_integer_bits() const;

  inline void set_integer_bits(unsigned b)
  {
    set(ID_integer_bits, b);
  }

  inline friend const fixedbv_typet &to_fixedbv_type(const typet &type)
  {
    assert(type.id()==ID_fixedbv);
    return static_cast<const fixedbv_typet &>(type);
  }
};

/*! \brief Cast a generic typet to a \ref fixedbv_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * fixedbv_typet.
 *
 * \param type Source type
 * \return Object of type \ref fixedbv_typet
 *
 * \ingroup gr_std_types
*/
const fixedbv_typet &to_fixedbv_type(const typet &type);

/*! \brief Fixed-width bit-vector with IEEE floating-point interpretation
*/
class floatbv_typet:public bitvector_typet
{
public:
  inline floatbv_typet():bitvector_typet(ID_floatbv)
  {
  }

  inline unsigned get_e() const
  {
    // subtract one for sign bit
    return get_width()-get_f()-1;
  }

  unsigned get_f() const;

  inline void set_f(unsigned b)
  {
    set(ID_f, b);
  }

  inline friend const floatbv_typet &to_floatbv_type(const typet &type)
  {
    assert(type.id()==ID_floatbv);
    return static_cast<const floatbv_typet &>(type);
  }
};

/*! \brief Cast a generic typet to a \ref floatbv_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * floatbv_typet.
 *
 * \param type Source type
 * \return Object of type \ref floatbv_typet
 *
 * \ingroup gr_std_types
*/
const floatbv_typet &to_floatbv_type(const typet &type);

/*! \brief Type for c bit fields
*/
class c_bit_field_typet:public bitvector_typet
{
public:
  inline c_bit_field_typet():bitvector_typet(ID_c_bit_field)
  {
  }

  inline explicit c_bit_field_typet(const typet &subtype, unsigned width):
    bitvector_typet(ID_c_bit_field, subtype, width)
  {
  }

  inline friend const c_bit_field_typet &to_c_bit_field_type(const typet &type)
  {
    assert(type.id()==ID_c_bit_field);
    return static_cast<const c_bit_field_typet &>(type);
  }

  inline friend c_bit_field_typet &to_c_bit_field_type(typet &type)
  {
    assert(type.id()==ID_c_bit_field);
    return static_cast<c_bit_field_typet &>(type);
  }

  // These have a sub-type
};

/*! \brief Cast a generic typet to a \ref c_bit_field_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * c_bit_field_typet.
 *
 * \param type Source type
 * \return Object of type \ref c_bit_field_typet
 *
 * \ingroup gr_std_types
*/
const c_bit_field_typet &to_c_bit_field_type(const typet &type);

/*! \brief Cast a generic typet to a \ref c_bit_field_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * c_bit_field_typet.
 *
 * \param type Source type
 * \return Object of type \ref c_bit_field_typet
 *
 * \ingroup gr_std_types
*/
c_bit_field_typet &to_c_bit_field_type(typet &type);

/*! \brief The pointer type
*/
class pointer_typet:public bitvector_typet
{
public:
  inline pointer_typet():bitvector_typet(ID_pointer)
  {
  }

  inline explicit pointer_typet(const typet &_subtype):
    bitvector_typet(ID_pointer, _subtype)
  {
  }

  inline explicit pointer_typet(const typet &_subtype, unsigned width):
    bitvector_typet(ID_pointer, _subtype, width)
  {
  }
  
  inline signedbv_typet difference_type() const
  {
    return signedbv_typet(get_width());
  }
};

/*! \brief Cast a generic typet to a \ref pointer_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * pointer_typet.
 *
 * \param type Source type
 * \return Object of type \ref pointer_typet
 *
 * \ingroup gr_std_types
*/
extern inline const pointer_typet &to_pointer_type(const typet &type)
{
  assert(type.id()==ID_pointer);
  return static_cast<const pointer_typet &>(type);
}

/*! \copydoc to_pointer_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline pointer_typet &to_pointer_type(typet &type)
{
  assert(type.id()==ID_pointer);
  return static_cast<pointer_typet &>(type);
}

/*! \brief The reference type
*/
class reference_typet:public pointer_typet
{
public:
  inline reference_typet()
  {
    set(ID_C_reference, true);
  }

  inline explicit reference_typet(const typet &_subtype):pointer_typet(_subtype)
  {
  }
};

/*! \brief TO_BE_DOCUMENTED
*/
bool is_reference(const typet &type);
/*! \brief TO_BE_DOCUMENTED
*/
bool is_rvalue_reference(const typet &type);

/*! \brief The C/C++ Booleans
*/
class c_bool_typet:public bitvector_typet
{
public:
  inline c_bool_typet():bitvector_typet(ID_c_bool)
  {
  }

  explicit inline c_bool_typet(unsigned width):
    bitvector_typet(ID_c_bool, width)
  {
  }
};

/*! \brief Cast a generic typet to a \ref c_bool_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * c_bool_typet.
 *
 * \param type Source type
 * \return Object of type \ref c_bool_typet
 *
 * \ingroup gr_std_types
*/
extern inline const c_bool_typet &to_c_bool_type(const typet &type)
{
  assert(type.id()==ID_c_bool);
  return static_cast<const c_bool_typet &>(type);
}

/*! \copydoc to_c_bool_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline c_bool_typet &to_c_bool_type(typet &type)
{
  assert(type.id()==ID_c_bool);
  return static_cast<c_bool_typet &>(type);
}

/*! \brief TO_BE_DOCUMENTED
*/
class string_typet:public typet
{
public:
  inline string_typet():typet(ID_string)
  {
  }

  inline friend const string_typet &to_string_type(const typet &type)
  {
    assert(type.id()==ID_string);
    return static_cast<const string_typet &>(type);
  }
};

/*! \brief Cast a generic typet to a \ref string_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * string_typet.
 *
 * \param type Source type
 * \return Object of type \ref string_typet
 *
 * \ingroup gr_std_types
*/
const string_typet &to_string_type(const typet &type);

/*! \brief A type for subranges of integers
*/
class range_typet:public typet
{
public:
  inline range_typet():typet(ID_range)
  {
  }
  
  inline range_typet(const mp_integer &_from, const mp_integer &_to)
  {
    set_from(_from);
    set_to(_to);
  }

  inline friend const range_typet &to_range_type(const typet &type)
  {
    assert(type.id()==ID_range);
    return static_cast<const range_typet &>(type);
  }

  mp_integer get_from() const;
  mp_integer get_to() const;

  void set_from(const mp_integer &_from);
  void set_to(const mp_integer &to);
};

/*! \brief Cast a generic typet to a \ref range_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * range_typet.
 *
 * \param type Source type
 * \return Object of type \ref range_typet
 *
 * \ingroup gr_std_types
*/
const range_typet &to_range_type(const typet &type);

/*! \brief A constant-size array type
*/
class vector_typet:public type_with_subtypet
{
public:
  inline vector_typet():type_with_subtypet(ID_vector)
  {
  }
  
  inline vector_typet(const typet &_subtype,
                      const exprt &_size):type_with_subtypet(ID_vector, _subtype)
  {
    size()=_size;
  }
  
  inline const exprt &size() const
  {
    return static_cast<const exprt &>(find(ID_size));
  }
  
  inline exprt &size()
  {
    return static_cast<exprt &>(add(ID_size));
  }

};

/*! \brief Cast a generic typet to a \ref vector_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * vector_typet.
 *
 * \param type Source type
 * \return Object of type \ref vector_typet
 *
 * \ingroup gr_std_types
*/
extern inline const vector_typet &to_vector_type(const typet &type)
{
  assert(type.id()==ID_vector);
  return static_cast<const vector_typet &>(type);
}

/*! \copydoc to_vector_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline vector_typet &to_vector_type(typet &type)
{
  assert(type.id()==ID_vector);
  return static_cast<vector_typet &>(type);
}

/*! \brief Complex numbers made of pair of given subtype
*/
class complex_typet:public type_with_subtypet
{
public:
  inline complex_typet():type_with_subtypet(ID_complex)
  {
  }
  
  explicit inline complex_typet(const typet &_subtype):
    type_with_subtypet(ID_complex, _subtype)
  {
  }
};

/*! \brief Cast a generic typet to a \ref complex_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * complex_typet.
 *
 * \param type Source type
 * \return Object of type \ref complex_typet
 *
 * \ingroup gr_std_types
*/
extern inline const complex_typet &to_complex_type(const typet &type)
{
  assert(type.id()==ID_complex);
  return static_cast<const complex_typet &>(type);
}

/*! \copydoc to_complex_type(const typet &)
 * \ingroup gr_std_types
*/
extern inline complex_typet &to_complex_type(typet &type)
{
  assert(type.id()==ID_complex);
  return static_cast<complex_typet &>(type);
}

#endif
