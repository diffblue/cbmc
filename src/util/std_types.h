/*******************************************************************\

Module: Pre-defined types

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Pre-defined types

#ifndef CPROVER_UTIL_STD_TYPES_H
#define CPROVER_UTIL_STD_TYPES_H

#include "expr.h"
#include "expr_cast.h"
#include "invariant.h"
#include "mp_arith.h"
#include "validate.h"

#include <unordered_map>

class constant_exprt;
class namespacet;

/// This method tests,
/// if the given typet is a constant
inline bool is_constant(const typet &type)
{
  return type.get_bool(ID_C_constant);
}

/// The Boolean type
class bool_typet:public typet
{
public:
  bool_typet():typet(ID_bool)
  {
  }
};

template <>
inline bool can_cast_type<bool_typet>(const typet &base)
{
  return base.id() == ID_bool;
}

/// The empty type
class empty_typet:public typet
{
public:
  empty_typet():typet(ID_empty)
  {
  }
};

/// Base type for structs and unions
///
/// For example C structs, C unions, C++ classes, Java classes.
class struct_union_typet:public typet
{
public:
  explicit struct_union_typet(const irep_idt &_id):typet(_id)
  {
  }

  class componentt:public exprt
  {
  public:
    componentt() = default;

    componentt(const irep_idt &_name, typet _type)
    {
      set_name(_name);
      type().swap(_type);
    }

    const irep_idt &get_name() const
    {
      return get(ID_name);
    }

    void set_name(const irep_idt &name)
    {
      return set(ID_name, name);
    }

    const irep_idt &get_base_name() const
    {
      return get(ID_base_name);
    }

    void set_base_name(const irep_idt &base_name)
    {
      return set(ID_base_name, base_name);
    }

    const irep_idt &get_access() const
    {
      return get(ID_access);
    }

    void set_access(const irep_idt &access)
    {
      return set(ID_access, access);
    }

    const irep_idt &get_pretty_name() const
    {
      return get(ID_pretty_name);
    }

    void set_pretty_name(const irep_idt &name)
    {
      return set(ID_pretty_name, name);
    }

    bool get_anonymous() const
    {
      return get_bool(ID_anonymous);
    }

    void set_anonymous(bool anonymous)
    {
      return set(ID_anonymous, anonymous);
    }

    bool get_is_padding() const
    {
      return get_bool(ID_C_is_padding);
    }

    void set_is_padding(bool is_padding)
    {
      return set(ID_C_is_padding, is_padding);
    }
  };

  typedef std::vector<componentt> componentst;

  struct_union_typet(const irep_idt &_id, componentst _components) : typet(_id)
  {
    components() = std::move(_components);
  }

  const componentst &components() const
  {
    return (const componentst &)(find(ID_components).get_sub());
  }

  componentst &components()
  {
    return (componentst &)(add(ID_components).get_sub());
  }

  bool has_component(const irep_idt &component_name) const
  {
    return get_component(component_name).is_not_nil();
  }

  const componentt &get_component(
    const irep_idt &component_name) const;

  std::size_t component_number(const irep_idt &component_name) const;
  const typet &component_type(const irep_idt &component_name) const;

  irep_idt get_tag() const { return get(ID_tag); }
  void set_tag(const irep_idt &tag) { set(ID_tag, tag); }

  /// A struct may be a class, where members may have access restrictions.
  bool is_class() const
  {
    return id() == ID_struct && get_bool(ID_C_class);
  }

  /// Return the access specification for members where access has not been
  /// modified.
  irep_idt default_access() const
  {
    return is_class() ? ID_private : ID_public;
  }

  /// A struct/union may be incomplete
  bool is_incomplete() const
  {
    return get_bool(ID_incomplete);
  }

  /// A struct/union may be incomplete
  void make_incomplete()
  {
    set(ID_incomplete, true);
  }
};

/// Check whether a reference to a typet is a \ref struct_union_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref struct_union_typet.
template <>
inline bool can_cast_type<struct_union_typet>(const typet &type)
{
  return type.id() == ID_struct || type.id() == ID_union;
}

/// \brief Cast a typet to a \ref struct_union_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// struct_union_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type
/// \return Object of type \ref struct_union_typet
inline const struct_union_typet &to_struct_union_type(const typet &type)
{
  PRECONDITION(can_cast_type<struct_union_typet>(type));
  return static_cast<const struct_union_typet &>(type);
}

/// \copydoc to_struct_union_type(const typet &)
inline struct_union_typet &to_struct_union_type(typet &type)
{
  PRECONDITION(can_cast_type<struct_union_typet>(type));
  return static_cast<struct_union_typet &>(type);
}

class struct_tag_typet;

/// Structure type, corresponds to C style structs
class struct_typet:public struct_union_typet
{
public:
  struct_typet():struct_union_typet(ID_struct)
  {
  }

  explicit struct_typet(componentst _components)
    : struct_union_typet(ID_struct, std::move(_components))
  {
  }

  bool is_prefix_of(const struct_typet &other) const;

  /// A struct may be a class, where members may have access restrictions.
  bool is_class() const
  {
    return get_bool(ID_C_class);
  }

  /// Base class or struct that a class or struct inherits from.
  class baset : public exprt
  {
  public:
    struct_tag_typet &type();
    const struct_tag_typet &type() const;
    explicit baset(struct_tag_typet base);
  };

  typedef std::vector<baset> basest;

  /// Get the collection of base classes/structs.
  const basest &bases() const
  {
    return (const basest &)find(ID_bases).get_sub();
  }

  /// Get the collection of base classes/structs.
  basest &bases()
  {
    return (basest &)add(ID_bases).get_sub();
  }

  /// Add a base class/struct
  /// \param base: Type of case/class struct to be added.
  void add_base(const struct_tag_typet &base);

  /// Return the base with the given name, if exists.
  /// \param id: The name of the base we are looking for.
  /// \return The base if exists.
  optionalt<baset> get_base(const irep_idt &id) const;

  /// Test whether `id` is a base class/struct.
  /// \param id: symbol type name
  /// \return True if, and only if, the symbol type `id` is a base class/struct.
  bool has_base(const irep_idt &id) const
  {
    return get_base(id).has_value();
  }
};

/// Check whether a reference to a typet is a \ref struct_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref struct_typet.
template <>
inline bool can_cast_type<struct_typet>(const typet &type)
{
  return type.id() == ID_struct;
}

/// \brief Cast a typet to a \ref struct_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// struct_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref struct_typet.
inline const struct_typet &to_struct_type(const typet &type)
{
  PRECONDITION(can_cast_type<struct_typet>(type));
  return static_cast<const struct_typet &>(type);
}

/// \copydoc to_struct_type(const typet &)
inline struct_typet &to_struct_type(typet &type)
{
  PRECONDITION(can_cast_type<struct_typet>(type));
  return static_cast<struct_typet &>(type);
}

/// Class type
///
/// For example, C++ and Java classes.
class class_typet:public struct_typet
{
public:
  class_typet():struct_typet()
  {
    set(ID_C_class, true);
  }

  typedef componentt methodt;
  typedef componentst methodst;

  const methodst &methods() const
  {
    return (const methodst &)(find(ID_methods).get_sub());
  }

  methodst &methods()
  {
    return (methodst &)(add(ID_methods).get_sub());
  }

  using static_membert = componentt;
  using static_memberst = componentst;

  const static_memberst &static_members() const
  {
    return (const static_memberst &)(find(ID_static_members).get_sub());
  }

  static_memberst &static_members()
  {
    return (static_memberst &)(add(ID_static_members).get_sub());
  }

  bool is_abstract() const
  {
    return get_bool(ID_abstract);
  }
};

/// Check whether a reference to a typet is a \ref class_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref class_typet.
template <>
inline bool can_cast_type<class_typet>(const typet &type)
{
  return can_cast_type<struct_typet>(type) && type.get_bool(ID_C_class);
}

/// \brief Cast a typet to a \ref class_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// class_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref class_typet.
inline const class_typet &to_class_type(const typet &type)
{
  PRECONDITION(can_cast_type<class_typet>(type));
  return static_cast<const class_typet &>(type);
}

/// \copydoc to_class_type(const typet &)
inline class_typet &to_class_type(typet &type)
{
  PRECONDITION(can_cast_type<class_typet>(type));
  return static_cast<class_typet &>(type);
}

/// A tag-based type, i.e., \ref typet with an identifier
class tag_typet:public typet
{
public:
  explicit tag_typet(
    const irep_idt &_id,
    const irep_idt &identifier):typet(_id)
  {
    set_identifier(identifier);
  }

  void set_identifier(const irep_idt &identifier)
  {
    set(ID_identifier, identifier);
  }

  const irep_idt &get_identifier() const
  {
    return get(ID_identifier);
  }
};

/// Check whether a reference to a typet is a \ref tag_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref tag_typet.
template <>
inline bool can_cast_type<tag_typet>(const typet &type)
{
  return type.id() == ID_c_enum_tag || type.id() == ID_struct_tag ||
         type.id() == ID_union_tag;
}

/// \brief Cast a typet to a \ref tag_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// tag_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref tag_typet.
inline const tag_typet &to_tag_type(const typet &type)
{
  PRECONDITION(can_cast_type<tag_typet>(type));
  return static_cast<const tag_typet &>(type);
}

/// \copydoc to_tag_type(const typet &)
inline tag_typet &to_tag_type(typet &type)
{
  PRECONDITION(can_cast_type<tag_typet>(type));
  return static_cast<tag_typet &>(type);
}

/// A struct tag type, i.e., \ref struct_typet with an identifier
class struct_tag_typet:public tag_typet
{
public:
  explicit struct_tag_typet(const irep_idt &identifier):
    tag_typet(ID_struct_tag, identifier)
  {
  }
};

/// Check whether a reference to a typet is a \ref struct_tag_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref struct_tag_typet.
template <>
inline bool can_cast_type<struct_tag_typet>(const typet &type)
{
  return type.id() == ID_struct_tag;
}

/// \brief Cast a typet to a \ref struct_tag_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// struct_tag_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref struct_tag_typet
inline const struct_tag_typet &to_struct_tag_type(const typet &type)
{
  PRECONDITION(can_cast_type<struct_tag_typet>(type));
  return static_cast<const struct_tag_typet &>(type);
}

/// \copydoc to_struct_tag_type(const typet &)
inline struct_tag_typet &to_struct_tag_type(typet &type)
{
  PRECONDITION(can_cast_type<struct_tag_typet>(type));
  return static_cast<struct_tag_typet &>(type);
}

/// An enumeration type, i.e., a type with elements (not to be confused with C
/// enums)
class enumeration_typet:public typet
{
public:
  enumeration_typet():typet(ID_enumeration)
  {
  }

  const irept::subt &elements() const
  {
    return find(ID_elements).get_sub();
  }

  irept::subt &elements()
  {
    return add(ID_elements).get_sub();
  }
};

/// Check whether a reference to a typet is a \ref enumeration_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref enumeration_typet.
template <>
inline bool can_cast_type<enumeration_typet>(const typet &type)
{
  return type.id() == ID_enumeration;
}

/// \brief Cast a typet to a \ref enumeration_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// enumeration_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref enumeration_typet.
inline const enumeration_typet &to_enumeration_type(const typet &type)
{
  PRECONDITION(can_cast_type<enumeration_typet>(type));
  return static_cast<const enumeration_typet &>(type);
}

/// \copydoc to_enumeration_type(const typet &)
inline enumeration_typet &to_enumeration_type(typet &type)
{
  PRECONDITION(can_cast_type<enumeration_typet>(type));
  return static_cast<enumeration_typet &>(type);
}

/// Base type of functions
class code_typet:public typet
{
public:
  class parametert;
  typedef std::vector<parametert> parameterst;

  /// Constructs a new code type, i.e., function type.
  /// \param _parameters: The vector of function parameters.
  /// \param _return_type: The return type.
  code_typet(parameterst _parameters, typet _return_type) : typet(ID_code)
  {
    parameters().swap(_parameters);
    return_type().swap(_return_type);
  }

  // used to be argumentt -- now uses standard terminology

  class parametert:public exprt
  {
  public:
    explicit parametert(const typet &type):exprt(ID_parameter, type)
    {
    }

    const exprt &default_value() const
    {
      return find_expr(ID_C_default_value);
    }

    bool has_default_value() const
    {
      return default_value().is_not_nil();
    }

    exprt &default_value()
    {
      return add_expr(ID_C_default_value);
    }

    // The following for methods will go away;
    // these should not be part of the signature of a function,
    // but rather part of the body.
    void set_identifier(const irep_idt &identifier)
    {
      set(ID_C_identifier, identifier);
    }

    void set_base_name(const irep_idt &name)
    {
      set(ID_C_base_name, name);
    }

    const irep_idt &get_identifier() const
    {
      return get(ID_C_identifier);
    }

    const irep_idt &get_base_name() const
    {
      return get(ID_C_base_name);
    }

    bool get_this() const
    {
      return get_bool(ID_C_this);
    }

    void set_this()
    {
      set(ID_C_this, true);
    }
  };

  bool has_ellipsis() const
  {
    return find(ID_parameters).get_bool(ID_ellipsis);
  }

  bool has_this() const
  {
    return get_this() != nullptr;
  }

  const parametert *get_this() const
  {
    const parameterst &p=parameters();
    if(!p.empty() && p.front().get_this())
      return &p.front();
    else
      return nullptr;
  }

  bool is_KnR() const
  {
    return get_bool(ID_C_KnR);
  }

  void make_ellipsis()
  {
    add(ID_parameters).set(ID_ellipsis, true);
  }

  void remove_ellipsis()
  {
    add(ID_parameters).remove(ID_ellipsis);
  }

  const typet &return_type() const
  {
    return find_type(ID_return_type);
  }

  typet &return_type()
  {
    return add_type(ID_return_type);
  }

  const parameterst &parameters() const
  {
    return (const parameterst &)find(ID_parameters).get_sub();
  }

  parameterst &parameters()
  {
    return (parameterst &)add(ID_parameters).get_sub();
  }

  bool get_inlined() const
  {
    return get_bool(ID_C_inlined);
  }

  void set_inlined(bool value)
  {
    set(ID_C_inlined, value);
  }

  const irep_idt &get_access() const
  {
    return get(ID_access);
  }

  void set_access(const irep_idt &access)
  {
    return set(ID_access, access);
  }

  bool get_is_constructor() const
  {
    return get_bool(ID_constructor);
  }

  void set_is_constructor()
  {
    set(ID_constructor, true);
  }

  /// Produces the list of parameter identifiers.
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

  typedef std::unordered_map<irep_idt, std::size_t> parameter_indicest;

  /// Get a map from parameter name to its index.
  parameter_indicest parameter_indices() const
  {
    parameter_indicest parameter_indices;
    const parameterst &params = parameters();
    parameter_indices.reserve(params.size());
    std::size_t index = 0;
    for(const auto &p : params)
    {
      const irep_idt &id = p.get_identifier();
      if(!id.empty())
        parameter_indices.insert({ id, index });
      ++index;
    }
    return parameter_indices;
  }
};

/// Check whether a reference to a typet is a \ref code_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref code_typet.
template <>
inline bool can_cast_type<code_typet>(const typet &type)
{
  return type.id() == ID_code;
}

/// \brief Cast a typet to a \ref code_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// code_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref code_typet.
inline const code_typet &to_code_type(const typet &type)
{
  PRECONDITION(can_cast_type<code_typet>(type));
  code_typet::check(type);
  return static_cast<const code_typet &>(type);
}

/// \copydoc to_code_type(const typet &)
inline code_typet &to_code_type(typet &type)
{
  PRECONDITION(can_cast_type<code_typet>(type));
  code_typet::check(type);
  return static_cast<code_typet &>(type);
}

/// Arrays with given size
///
/// Used for ordinary source-language arrays.
class array_typet:public type_with_subtypet
{
public:
  array_typet(typet _subtype, exprt _size)
    : type_with_subtypet(ID_array, std::move(_subtype))
  {
    add(ID_size, std::move(_size));
  }

  /// The type of the index expressions into any instance of this type.
  typet index_type() const;

  /// The type of the elements of the array.
  /// This method is preferred over .subtype(),
  /// which will eventually be deprecated.
  const typet &element_type() const
  {
    return subtype();
  }

  /// The type of the elements of the array.
  /// This method is preferred over .subtype(),
  /// which will eventually be deprecated.
  typet &element_type()
  {
    return subtype();
  }

  const exprt &size() const
  {
    return static_cast<const exprt &>(find(ID_size));
  }

  exprt &size()
  {
    return static_cast<exprt &>(add(ID_size));
  }

  bool is_complete() const
  {
    return size().is_not_nil();
  }

  bool is_incomplete() const
  {
    return size().is_nil();
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT);
};

/// Check whether a reference to a typet is a \ref array_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref array_typet.
template <>
inline bool can_cast_type<array_typet>(const typet &type)
{
  return type.id() == ID_array;
}

/// \brief Cast a typet to an \ref array_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// array_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref array_typet.
inline const array_typet &to_array_type(const typet &type)
{
  PRECONDITION(can_cast_type<array_typet>(type));
  array_typet::check(type);
  return static_cast<const array_typet &>(type);
}

/// \copydoc to_array_type(const typet &)
inline array_typet &to_array_type(typet &type)
{
  PRECONDITION(can_cast_type<array_typet>(type));
  array_typet::check(type);
  return static_cast<array_typet &>(type);
}

/// Base class of fixed-width bit-vector types
///
/// Superclass of anything represented by bits, for example integers (in 32
/// or 64-bit representation), floating point numbers etc. In contrast, \ref
/// integer_typet is a direct integer representation.
class bitvector_typet : public typet
{
public:
  explicit bitvector_typet(const irep_idt &_id) : typet(_id)
  {
  }

  bitvector_typet(const irep_idt &_id, std::size_t width) : typet(_id)
  {
    set_width(width);
  }

  std::size_t get_width() const
  {
    return get_size_t(ID_width);
  }

  void set_width(std::size_t width)
  {
    set_size_t(ID_width, width);
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm, !type.get(ID_width).empty(), "bitvector type must have width");
  }
};

/// Check whether a reference to a typet is a \ref bitvector_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref bitvector_typet.
template <>
inline bool can_cast_type<bitvector_typet>(const typet &type)
{
  return type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
         type.id() == ID_fixedbv || type.id() == ID_floatbv ||
         type.id() == ID_verilog_signedbv ||
         type.id() == ID_verilog_unsignedbv || type.id() == ID_bv ||
         type.id() == ID_pointer || type.id() == ID_c_bit_field ||
         type.id() == ID_c_bool;
}

/// String type
///
/// Represents string constants, such as `@class_identifier`.
class string_typet:public typet
{
public:
  string_typet():typet(ID_string)
  {
  }
};

/// Check whether a reference to a typet is a \ref string_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref string_typet.
template <>
inline bool can_cast_type<string_typet>(const typet &type)
{
  return type.id() == ID_string;
}

/// \brief Cast a typet to a \ref string_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// string_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref string_typet.
inline const string_typet &to_string_type(const typet &type)
{
  PRECONDITION(can_cast_type<string_typet>(type));
  return static_cast<const string_typet &>(type);
}

/// \copydoc to_string_type(const typet &)
inline string_typet &to_string_type(typet &type)
{
  PRECONDITION(can_cast_type<string_typet>(type));
  return static_cast<string_typet &>(type);
}

/// A type for subranges of integers
class range_typet:public typet
{
public:
  range_typet(const mp_integer &_from, const mp_integer &_to) : typet(ID_range)
  {
    set_from(_from);
    set_to(_to);
  }

  mp_integer get_from() const;
  mp_integer get_to() const;

  void set_from(const mp_integer &_from);
  void set_to(const mp_integer &to);
};

/// Check whether a reference to a typet is a \ref range_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref range_typet.
template <>
inline bool can_cast_type<range_typet>(const typet &type)
{
  return type.id() == ID_range;
}

/// \brief Cast a typet to a \ref range_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// range_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref range_typet.
inline const range_typet &to_range_type(const typet &type)
{
  PRECONDITION(can_cast_type<range_typet>(type));
  return static_cast<const range_typet &>(type);
}

/// \copydoc to_range_type(const typet &)
inline range_typet &to_range_type(typet &type)
{
  PRECONDITION(can_cast_type<range_typet>(type));
  return static_cast<range_typet &>(type);
}

/// The vector type
///
/// Used to represent the short vectors used by CPU instruction sets such as
/// MMX, SSE and AVX. They all provide registers that are something like
/// 8 x int32, for example, and corresponding operations that operate
/// element-wise on their operand vectors. Compared to \ref array_typet,
/// vector_typet has a fixed size whereas array_typet has no element-wise
/// operators.
/// Note that `remove_vector.h` removes this data type by compilation into
/// arrays.
class vector_typet:public type_with_subtypet
{
public:
  vector_typet(const typet &_subtype, const constant_exprt &_size);

  /// The type of any index expression into an instance of this type.
  typet index_type() const;

  /// The type of the elements of the vector.
  /// This method is preferred over .subtype(),
  /// which will eventually be deprecated.
  const typet &element_type() const
  {
    return subtype();
  }

  /// The type of the elements of the vector.
  /// This method is preferred over .subtype(),
  /// which will eventually be deprecated.
  typet &element_type()
  {
    return subtype();
  }

  const constant_exprt &size() const;
  constant_exprt &size();
};

/// Check whether a reference to a typet is a \ref vector_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref vector_typet.
template <>
inline bool can_cast_type<vector_typet>(const typet &type)
{
  return type.id() == ID_vector;
}

/// \brief Cast a typet to a \ref vector_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// vector_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref vector_typet.
inline const vector_typet &to_vector_type(const typet &type)
{
  PRECONDITION(can_cast_type<vector_typet>(type));
  type_with_subtypet::check(type);
  return static_cast<const vector_typet &>(type);
}

/// \copydoc to_vector_type(const typet &)
inline vector_typet &to_vector_type(typet &type)
{
  PRECONDITION(can_cast_type<vector_typet>(type));
  type_with_subtypet::check(type);
  return static_cast<vector_typet &>(type);
}

/// Complex numbers made of pair of given subtype
class complex_typet:public type_with_subtypet
{
public:
  explicit complex_typet(typet _subtype)
    : type_with_subtypet(ID_complex, std::move(_subtype))
  {
  }
};

/// Check whether a reference to a typet is a \ref complex_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref complex_typet.
template <>
inline bool can_cast_type<complex_typet>(const typet &type)
{
  return type.id() == ID_complex;
}

/// \brief Cast a typet to a \ref complex_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// complex_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref complex_typet.
inline const complex_typet &to_complex_type(const typet &type)
{
  PRECONDITION(can_cast_type<complex_typet>(type));
  type_with_subtypet::check(type);
  return static_cast<const complex_typet &>(type);
}

/// \copydoc to_complex_type(const typet &)
inline complex_typet &to_complex_type(typet &type)
{
  PRECONDITION(can_cast_type<complex_typet>(type));
  type_with_subtypet::check(type);
  return static_cast<complex_typet &>(type);
}

bool is_constant_or_has_constant_components(
  const typet &type,
  const namespacet &ns);

#endif // CPROVER_UTIL_STD_TYPES_H
