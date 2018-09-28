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
#include "mp_arith.h"
#include "invariant.h"
#include "expr_cast.h"

#include <unordered_map>

class constant_exprt;
class namespacet;

/// The Boolean type
class bool_typet:public typet
{
public:
  bool_typet():typet(ID_bool)
  {
  }
};

/// The NIL type, i.e., an invalid type, no value.
/// \deprecated Use `optional<typet>` instead.
// NOLINTNEXTLINE
class DEPRECATED("Use `optional<typet>` instead.") nil_typet : public typet
{
public:
  nil_typet():typet(static_cast<const typet &>(get_nil_irep()))
  {
  }
};

/// The empty type
class empty_typet:public typet
{
public:
  empty_typet():typet(ID_empty)
  {
  }
};

/// The void type, the same as \ref empty_typet.
class void_typet:public empty_typet
{
};

/// A reference into the symbol table
class symbol_typet:public typet
{
public:
  explicit symbol_typet(const irep_idt &identifier) : typet(ID_symbol_type)
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

/// Check whether a reference to a typet is a \ref symbol_typet.
/// \param type Source type.
/// \return True if \param type is a \ref symbol_typet.
template <>
inline bool can_cast_type<symbol_typet>(const typet &type)
{
  return type.id() == ID_symbol_type;
}

/// \brief Cast a typet to a \ref symbol_typet.
///
/// This is an unchecked conversion. \a type must be known to be
/// \ref symbol_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref symbol_typet.
inline const symbol_typet &to_symbol_type(const typet &type)
{
  PRECONDITION(can_cast_type<symbol_typet>(type));
  return static_cast<const symbol_typet &>(type);
}

/// \copydoc to_symbol_type(const typet &)
inline symbol_typet &to_symbol_type(typet &type)
{
  PRECONDITION(can_cast_type<symbol_typet>(type));
  return static_cast<symbol_typet &>(type);
}

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
    componentt()
    {
    }

    componentt(const irep_idt &_name, const typet &_type)
    {
      set_name(_name);
      type()=_type;
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

    bool get_is_final() const
    {
      return get_bool(ID_final);
    }

    void set_is_final(const bool is_final)
    {
      set(ID_final, is_final);
    }
  };

  typedef std::vector<componentt> componentst;

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
};

/// Check whether a reference to a typet is a \ref struct_union_typet.
/// \param type Source type.
/// \return True if \param type is a \ref struct_union_typet.
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
/// \param type Source type
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

/// Structure type, corresponds to C style structs
class struct_typet:public struct_union_typet
{
public:
  struct_typet():struct_union_typet(ID_struct)
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
    explicit baset(const typet &base) : exprt(ID_base, base)
    {
    }
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
  void add_base(const symbol_typet &base)
  {
    bases().push_back(baset(base));
  }

  /// Return the base with the given name, if exists.
  /// \param id The name of the base we are looking for.
  /// \return The base if exists.
  optionalt<baset> get_base(const irep_idt &id) const
  {
    for(const auto &b : bases())
    {
      if(to_symbol_type(b.type()).get_identifier() == id)
        return b;
    }
    return {};
  }

  /// Test whether `id` is a base class/struct.
  /// \param id: symbol type name
  /// \return True if, and only if, the symbol type `id` is a base class/struct.
  bool has_base(const irep_idt &id) const
  {
    return get_base(id).has_value();
  }
};

/// Check whether a reference to a typet is a \ref struct_typet.
/// \param type Source type.
/// \return True if \param type is a \ref struct_typet.
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
/// \param type Source type.
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

  componentst &methods()
  {
    return (methodst &)(add(ID_methods).get_sub());
  }

  bool is_abstract() const
  {
    return get_bool(ID_abstract);
  }
};

/// Check whether a reference to a typet is a \ref class_typet.
/// \param type Source type.
/// \return True if \param type is a \ref class_typet.
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
/// \param type Source type.
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

/// The union type
///
/// For example, C union.
class union_typet:public struct_union_typet
{
public:
  union_typet():struct_union_typet(ID_union)
  {
  }
};

/// Check whether a reference to a typet is a \ref union_typet.
/// \param type Source type.
/// \return True if \param type is a \ref union_typet.
template <>
inline bool can_cast_type<union_typet>(const typet &type)
{
  return type.id() == ID_union;
}

/// \brief Cast a typet to a \ref union_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// union_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref union_typet
inline const union_typet &to_union_type(const typet &type)
{
  PRECONDITION(can_cast_type<union_typet>(type));
  return static_cast<const union_typet &>(type);
}

/// \copydoc to_union_type(const typet &)
inline union_typet &to_union_type(typet &type)
{
  PRECONDITION(can_cast_type<union_typet>(type));
  return static_cast<union_typet &>(type);
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
/// \param type Source type.
/// \return True if \param type is a \ref tag_typet.
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
/// \param type Source type.
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
/// \param type Source type.
/// \return True if \param type is a \ref struct_tag_typet.
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
/// \param type Source type.
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

/// A union tag type, i.e., \ref union_typet with an identifier
class union_tag_typet:public tag_typet
{
public:
  explicit union_tag_typet(const irep_idt &identifier):
    tag_typet(ID_union_tag, identifier)
  {
  }
};

/// Check whether a reference to a typet is a \ref union_tag_typet.
/// \param type Source type.
/// \return True if \param type is a \ref union_tag_typet.
template <>
inline bool can_cast_type<union_tag_typet>(const typet &type)
{
  return type.id() == ID_union_tag;
}

/// \brief Cast a typet to a \ref union_tag_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// union_tag_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref union_tag_typet.
inline const union_tag_typet &to_union_tag_type(const typet &type)
{
  PRECONDITION(can_cast_type<union_tag_typet>(type));
  return static_cast<const union_tag_typet &>(type);
}

/// \copydoc to_union_tag_type(const typet &)
inline union_tag_typet &to_union_tag_type(typet &type)
{
  PRECONDITION(can_cast_type<union_tag_typet>(type));
  return static_cast<union_tag_typet &>(type);
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
/// \param type Source type.
/// \return True if \param type is a \ref enumeration_typet.
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
/// \param type Source type.
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

/// The type of C enums
class c_enum_typet:public type_with_subtypet
{
public:
  explicit c_enum_typet(const typet &_subtype):
    type_with_subtypet(ID_c_enum, _subtype)
  {
  }

  class c_enum_membert:public irept
  {
  public:
    irep_idt get_value() const { return get(ID_value); }
    void set_value(const irep_idt &value) { set(ID_value, value); }
    irep_idt get_identifier() const { return get(ID_identifier); }
    void set_identifier(const irep_idt &identifier)
    {
      set(ID_identifier, identifier);
    }
    irep_idt get_base_name() const { return get(ID_base_name); }
    void set_base_name(const irep_idt &base_name)
    {
      set(ID_base_name, base_name);
    }
  };

  typedef std::vector<c_enum_membert> memberst;

  const memberst &members() const
  {
    return (const memberst &)(find(ID_body).get_sub());
  }
};

/// Check whether a reference to a typet is a \ref c_enum_typet.
/// \param type Source type.
/// \return True if \param type is a \ref c_enum_typet.
template <>
inline bool can_cast_type<c_enum_typet>(const typet &type)
{
  return type.id() == ID_c_enum;
}

/// \brief Cast a typet to a \ref c_enum_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// c_enum_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref c_enum_typet.
inline const c_enum_typet &to_c_enum_type(const typet &type)
{
  PRECONDITION(can_cast_type<c_enum_typet>(type));
  return static_cast<const c_enum_typet &>(type);
}

/// \copydoc to_c_enum_type(const typet &)
inline c_enum_typet &to_c_enum_type(typet &type)
{
  PRECONDITION(can_cast_type<c_enum_typet>(type));
  return static_cast<c_enum_typet &>(type);
}

/// C enum tag type, i.e., \ref c_enum_typet with an identifier
class c_enum_tag_typet:public tag_typet
{
public:
  explicit c_enum_tag_typet(const irep_idt &identifier):
    tag_typet(ID_c_enum_tag, identifier)
  {
  }
};

/// Check whether a reference to a typet is a \ref c_enum_tag_typet.
/// \param type Source type.
/// \return True if \param type is a \ref c_enum_tag_typet.
template <>
inline bool can_cast_type<c_enum_tag_typet>(const typet &type)
{
  return type.id() == ID_c_enum_tag;
}

/// \brief Cast a typet to a \ref c_enum_tag_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// c_enum_tag_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref c_enum_tag_typet.
inline const c_enum_tag_typet &to_c_enum_tag_type(const typet &type)
{
  PRECONDITION(can_cast_type<c_enum_tag_typet>(type));
  return static_cast<const c_enum_tag_typet &>(type);
}

/// \copydoc to_c_enum_tag_type(const typet &)
inline c_enum_tag_typet &to_c_enum_tag_type(typet &type)
{
  PRECONDITION(can_cast_type<c_enum_tag_typet>(type));
  return static_cast<c_enum_tag_typet &>(type);
}

/// Base type of functions
class code_typet:public typet
{
public:
  class parametert;
  typedef std::vector<parametert> parameterst;

  /// Constructs a new code type, i.e., function type.
  /// \param _parameters The vector of function parameters.
  /// \param _return_type The return type.
  code_typet(parameterst &&_parameters, typet &&_return_type) : typet(ID_code)
  {
    parameters().swap(_parameters);
    return_type().swap(_return_type);
  }

  /// Constructs a new code type, i.e., function type.
  /// \param _parameters The vector of function parameters.
  /// \param _return_type The return type.
  code_typet(parameterst &&_parameters, const typet &_return_type)
    : typet(ID_code)
  {
    parameters().swap(_parameters);
    return_type() = _return_type;
  }

  /// \deprecated
  DEPRECATED("Use the two argument constructor instead")
  code_typet():typet(ID_code)
  {
    // make sure these properties are always there to avoid problems
    // with irept comparisons
    add(ID_parameters);
    add_type(ID_return_type);
  }

  // used to be argumentt -- now uses standard terminology

  class parametert:public exprt
  {
  public:
    DEPRECATED("use parametert(type) instead")
    parametert():exprt(ID_parameter)
    {
    }

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
    const parameterst &p = parameters();
    parameter_indices.reserve(p.size());
    std::size_t index = 0;
    for(const auto &p : parameters())
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
/// \param type Source type.
/// \return True if \param type is a \ref code_typet.
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
/// \param type Source type.
/// \return Object of type \ref code_typet.
inline const code_typet &to_code_type(const typet &type)
{
  PRECONDITION(can_cast_type<code_typet>(type));
  validate_type(type);
  return static_cast<const code_typet &>(type);
}

/// \copydoc to_code_type(const typet &)
inline code_typet &to_code_type(typet &type)
{
  PRECONDITION(can_cast_type<code_typet>(type));
  validate_type(type);
  return static_cast<code_typet &>(type);
}

/// Arrays with given size
///
/// Used for ordinary source-language arrays.
class array_typet:public type_with_subtypet
{
public:
  array_typet(
    const typet &_subtype,
    const exprt &_size):type_with_subtypet(ID_array, _subtype)
  {
    size()=_size;
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
};

/// Check whether a reference to a typet is a \ref array_typet.
/// \param type Source type.
/// \return True if \param type is a \ref array_typet.
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
/// \param type Source type.
/// \return Object of type \ref array_typet.
inline const array_typet &to_array_type(const typet &type)
{
  PRECONDITION(can_cast_type<array_typet>(type));
  return static_cast<const array_typet &>(type);
}

/// \copydoc to_array_type(const typet &)
inline array_typet &to_array_type(typet &type)
{
  PRECONDITION(can_cast_type<array_typet>(type));
  return static_cast<array_typet &>(type);
}

/// Arrays without size
class incomplete_array_typet:public type_with_subtypet
{
public:
  incomplete_array_typet():type_with_subtypet(ID_incomplete_array)
  {
  }
};

/// Check whether a reference to a typet is a \ref incomplete_array_typet.
/// \param type Source type.
/// \return True if \param type is a \ref incomplete_array_typet.
template <>
inline bool can_cast_type<incomplete_array_typet>(const typet &type)
{
  return type.id() == ID_incomplete_array;
}

/// \brief Cast a typet to an \ref incomplete_array_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// incomplete_array_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref incomplete_array_typet.
inline const incomplete_array_typet &to_incomplete_array_type(const typet &type)
{
  PRECONDITION(can_cast_type<incomplete_array_typet>(type));
  return static_cast<const incomplete_array_typet &>(type);
}

/// \copydoc to_incomplete_array_type(const typet &)
inline incomplete_array_typet &to_incomplete_array_type(typet &type)
{
  PRECONDITION(can_cast_type<incomplete_array_typet>(type));
  return static_cast<incomplete_array_typet &>(type);
}

/// Base class of fixed-width bit-vector types
///
/// Superclass of anything represented by bits, for example integers (in 32
/// or 64-bit representation), floating point numbers etc. In contrast, \ref
/// integer_typet is a direct integer representation.
class bitvector_typet:public type_with_subtypet
{
public:
  explicit bitvector_typet(const irep_idt &_id):type_with_subtypet(_id)
  {
  }

  bitvector_typet(const irep_idt &_id, const typet &_subtype):
    type_with_subtypet(_id, _subtype)
  {
  }

  bitvector_typet(
    const irep_idt &_id,
    const typet &_subtype,
    std::size_t width):
    type_with_subtypet(_id, _subtype)
  {
    set_width(width);
  }

  bitvector_typet(const irep_idt &_id, std::size_t width):
    type_with_subtypet(_id)
  {
    set_width(width);
  }

  std::size_t get_width() const
  {
    return get_size_t(ID_width);
  }

  void set_width(std::size_t width)
  {
    set(ID_width, width);
  }
};

/// Check whether a reference to a typet is a \ref bitvector_typet.
/// \param type Source type.
/// \return True if \param type is a \ref bitvector_typet.
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

/// \brief Cast a typet to a \ref bitvector_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// bitvector_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref bitvector_typet.
inline const bitvector_typet &to_bitvector_type(const typet &type)
{
  PRECONDITION(can_cast_type<bitvector_typet>(type));

  return static_cast<const bitvector_typet &>(type);
}

/// \copydoc to_bitvector_type(const typet &type)
inline bitvector_typet &to_bitvector_type(typet &type)
{
  PRECONDITION(can_cast_type<bitvector_typet>(type));

  return static_cast<bitvector_typet &>(type);
}

/// Fixed-width bit-vector without numerical interpretation
class bv_typet:public bitvector_typet
{
public:
  explicit bv_typet(std::size_t width):bitvector_typet(ID_bv)
  {
    set_width(width);
  }
};

/// Check whether a reference to a typet is a \ref bv_typet.
/// \param type Source type.
/// \return True if \param type is a \ref bv_typet.
template <>
inline bool can_cast_type<bv_typet>(const typet &type)
{
  return type.id() == ID_bv;
}

inline void validate_type(const bv_typet &type)
{
  DATA_INVARIANT(!type.get(ID_width).empty(), "bitvector type must have width");
}

/// \brief Cast a typet to a \ref bv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// bv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref bv_typet.
inline const bv_typet &to_bv_type(const typet &type)
{
  PRECONDITION(can_cast_type<bv_typet>(type));
  const bv_typet &ret = static_cast<const bv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// \copydoc to_bv_type(const typet &)
inline bv_typet &to_bv_type(typet &type)
{
  PRECONDITION(can_cast_type<bv_typet>(type));
  bv_typet &ret = static_cast<bv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// Fixed-width bit-vector with unsigned binary interpretation
class unsignedbv_typet:public bitvector_typet
{
public:
  explicit unsignedbv_typet(std::size_t width):
    bitvector_typet(ID_unsignedbv, width)
  {
  }

  mp_integer smallest() const;
  mp_integer largest() const;
  constant_exprt smallest_expr() const;
  constant_exprt zero_expr() const;
  constant_exprt largest_expr() const;
};

/// Check whether a reference to a typet is a \ref unsignedbv_typet.
/// \param type Source type.
/// \return True if \param type is a \ref unsignedbv_typet.
template <>
inline bool can_cast_type<unsignedbv_typet>(const typet &type)
{
  return type.id() == ID_unsignedbv;
}

inline void validate_type(const unsignedbv_typet &type)
{
  DATA_INVARIANT(
    !type.get(ID_width).empty(), "unsigned bitvector type must have width");
}

/// \brief Cast a typet to an \ref unsignedbv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// unsignedbv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref unsignedbv_typet.
inline const unsignedbv_typet &to_unsignedbv_type(const typet &type)
{
  PRECONDITION(can_cast_type<unsignedbv_typet>(type));
  const unsignedbv_typet &ret = static_cast<const unsignedbv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// \copydoc to_unsignedbv_type(const typet &)
inline unsignedbv_typet &to_unsignedbv_type(typet &type)
{
  PRECONDITION(can_cast_type<unsignedbv_typet>(type));
  unsignedbv_typet &ret = static_cast<unsignedbv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// Fixed-width bit-vector with two's complement interpretation
class signedbv_typet:public bitvector_typet
{
public:
  explicit signedbv_typet(std::size_t width):
    bitvector_typet(ID_signedbv, width)
  {
  }

  mp_integer smallest() const;
  mp_integer largest() const;
  constant_exprt smallest_expr() const;
  constant_exprt zero_expr() const;
  constant_exprt largest_expr() const;
};

/// Check whether a reference to a typet is a \ref signedbv_typet.
/// \param type Source type.
/// \return True if \param type is a \ref signedbv_typet.
template <>
inline bool can_cast_type<signedbv_typet>(const typet &type)
{
  return type.id() == ID_signedbv;
}

inline void validate_type(const signedbv_typet &type)
{
  DATA_INVARIANT(
    !type.get(ID_width).empty(), "signed bitvector type must have width");
}

/// \brief Cast a typet to a \ref signedbv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// signedbv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref signedbv_typet.
inline const signedbv_typet &to_signedbv_type(const typet &type)
{
  PRECONDITION(can_cast_type<signedbv_typet>(type));
  const signedbv_typet &ret = static_cast<const signedbv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// \copydoc to_signedbv_type(const typet &)
inline signedbv_typet &to_signedbv_type(typet &type)
{
  PRECONDITION(can_cast_type<signedbv_typet>(type));
  signedbv_typet &ret = static_cast<signedbv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// Fixed-width bit-vector with signed fixed-point interpretation
///
/// Integer and fraction bits refer to the number of bits before and after
/// the decimal point, respectively. The width is the sum of the two.
class fixedbv_typet:public bitvector_typet
{
public:
  fixedbv_typet():bitvector_typet(ID_fixedbv)
  {
  }

  std::size_t get_fraction_bits() const
  {
    return get_width()-get_integer_bits();
  }

  std::size_t get_integer_bits() const;

  void set_integer_bits(std::size_t b)
  {
    set(ID_integer_bits, b);
  }
};

/// Check whether a reference to a typet is a \ref fixedbv_typet.
/// \param type Source type.
/// \return True if \param type is a \ref fixedbv_typet.
template <>
inline bool can_cast_type<fixedbv_typet>(const typet &type)
{
  return type.id() == ID_fixedbv;
}

inline void validate_type(const fixedbv_typet &type)
{
  DATA_INVARIANT(
    !type.get(ID_width).empty(), "fixed bitvector type must have width");
}

/// \brief Cast a typet to a \ref fixedbv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// fixedbv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref fixedbv_typet.
inline const fixedbv_typet &to_fixedbv_type(const typet &type)
{
  PRECONDITION(can_cast_type<fixedbv_typet>(type));
  const fixedbv_typet &ret = static_cast<const fixedbv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// \copydoc to_fixedbv_type(const typet &)
inline fixedbv_typet &to_fixedbv_type(typet &type)
{
  PRECONDITION(can_cast_type<fixedbv_typet>(type));
  fixedbv_typet &ret = static_cast<fixedbv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// Fixed-width bit-vector with IEEE floating-point interpretation
class floatbv_typet:public bitvector_typet
{
public:
  floatbv_typet():bitvector_typet(ID_floatbv)
  {
  }

  std::size_t get_e() const
  {
    // subtract one for sign bit
    return get_width()-get_f()-1;
  }

  std::size_t get_f() const;

  void set_f(std::size_t b)
  {
    set(ID_f, b);
  }
};

/// Check whether a reference to a typet is a \ref floatbv_typet.
/// \param type Source type.
/// \return True if \param type is a \ref floatbv_typet.
template <>
inline bool can_cast_type<floatbv_typet>(const typet &type)
{
  return type.id() == ID_floatbv;
}

inline void validate_type(const floatbv_typet &type)
{
  DATA_INVARIANT(
    !type.get(ID_width).empty(), "float bitvector type must have width");
}

/// \brief Cast a typet to a \ref floatbv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// floatbv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref floatbv_typet.
inline const floatbv_typet &to_floatbv_type(const typet &type)
{
  PRECONDITION(can_cast_type<floatbv_typet>(type));
  const floatbv_typet &ret = static_cast<const floatbv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// \copydoc to_floatbv_type(const typet &)
inline floatbv_typet &to_floatbv_type(typet &type)
{
  PRECONDITION(can_cast_type<floatbv_typet>(type));
  floatbv_typet &ret = static_cast<floatbv_typet &>(type);
  validate_type(ret);
  return ret;
}

/// Type for C bit fields
class c_bit_field_typet:public bitvector_typet
{
public:
  explicit c_bit_field_typet(const typet &subtype, std::size_t width):
    bitvector_typet(ID_c_bit_field, subtype, width)
  {
  }

  // These have a sub-type
};

/// Check whether a reference to a typet is a \ref c_bit_field_typet.
/// \param type Source type.
/// \return True if \param type is a \ref c_bit_field_typet.
template <>
inline bool can_cast_type<c_bit_field_typet>(const typet &type)
{
  return type.id() == ID_c_bit_field;
}

/// \brief Cast a typet to a \ref c_bit_field_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// c_bit_field_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref c_bit_field_typet.
inline const c_bit_field_typet &to_c_bit_field_type(const typet &type)
{
  PRECONDITION(can_cast_type<c_bit_field_typet>(type));
  return static_cast<const c_bit_field_typet &>(type);
}

/// \copydoc to_c_bit_field_type(const typet &type)
inline c_bit_field_typet &to_c_bit_field_type(typet &type)
{
  PRECONDITION(can_cast_type<c_bit_field_typet>(type));
  return static_cast<c_bit_field_typet &>(type);
}

/// The pointer type
class pointer_typet:public bitvector_typet
{
public:
  pointer_typet(const typet &_subtype, std::size_t width):
    bitvector_typet(ID_pointer, _subtype, width)
  {
  }

  signedbv_typet difference_type() const
  {
    return signedbv_typet(get_width());
  }
};

/// Check whether a reference to a typet is a \ref pointer_typet.
/// \param type Source type.
/// \return True if \param type is a \ref pointer_typet.
template <>
inline bool can_cast_type<pointer_typet>(const typet &type)
{
  return type.id() == ID_pointer;
}

inline void validate_type(const pointer_typet &type)
{
  DATA_INVARIANT(!type.get(ID_width).empty(), "pointer must have width");
}

/// \brief Cast a typet to a \ref pointer_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// pointer_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref pointer_typet.
inline const pointer_typet &to_pointer_type(const typet &type)
{
  PRECONDITION(can_cast_type<pointer_typet>(type));
  const pointer_typet &ret = static_cast<const pointer_typet &>(type);
  validate_type(ret);
  return ret;
}

/// \copydoc to_pointer_type(const typet &)
inline pointer_typet &to_pointer_type(typet &type)
{
  PRECONDITION(can_cast_type<pointer_typet>(type));
  pointer_typet &ret = static_cast<pointer_typet &>(type);
  validate_type(ret);
  return ret;
}

/// The reference type
///
/// Intends to model C++ reference. Comparing to \ref pointer_typet should
/// never be null.
class reference_typet:public pointer_typet
{
public:
  reference_typet(const typet &_subtype, std::size_t _width):
    pointer_typet(_subtype, _width)
  {
    set(ID_C_reference, true);
  }
};

/// Check whether a reference to a typet is a \ref reference_typet.
/// \param type Source type.
/// \return True if \param type is a \ref reference_typet.
template <>
inline bool can_cast_type<reference_typet>(const typet &type)
{
  return can_cast_type<pointer_typet>(type) && type.get_bool(ID_C_reference) &&
         !type.get(ID_width).empty();
}

/// \brief Cast a typet to a \ref reference_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// reference_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref reference_typet.
inline const reference_typet &to_reference_type(const typet &type)
{
  PRECONDITION(can_cast_type<reference_typet>(type));
  return static_cast<const reference_typet &>(type);
}

/// \copydoc to_reference_type(const typet &)
inline reference_typet &to_reference_type(typet &type)
{
  PRECONDITION(can_cast_type<reference_typet>(type));
  return static_cast<reference_typet &>(type);
}

bool is_reference(const typet &type);

bool is_rvalue_reference(const typet &type);

/// The C/C++ Booleans
class c_bool_typet:public bitvector_typet
{
public:
  c_bool_typet():bitvector_typet(ID_c_bool)
  {
  }

  explicit c_bool_typet(std::size_t width):
    bitvector_typet(ID_c_bool, width)
  {
  }
};

/// Check whether a reference to a typet is a \ref c_bool_typet.
/// \param type Source type.
/// \return True if \param type is a \ref c_bool_typet.
template <>
inline bool can_cast_type<c_bool_typet>(const typet &type)
{
  return type.id() == ID_c_bool;
}

inline void validate_type(const c_bool_typet &type)
{
  DATA_INVARIANT(!type.get(ID_width).empty(), "C bool type must have width");
}

/// \brief Cast a typet to a \ref c_bool_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// c_bool_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type Source type.
/// \return Object of type \ref c_bool_typet.
inline const c_bool_typet &to_c_bool_type(const typet &type)
{
  PRECONDITION(can_cast_type<c_bool_typet>(type));
  const c_bool_typet &ret = static_cast<const c_bool_typet &>(type);
  validate_type(ret);
  return ret;
}

/// \copydoc to_c_bool_type(const typet &)
inline c_bool_typet &to_c_bool_type(typet &type)
{
  PRECONDITION(can_cast_type<c_bool_typet>(type));
  c_bool_typet &ret = static_cast<c_bool_typet &>(type);
  validate_type(ret);
  return ret;
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
/// \param type Source type.
/// \return True if \param type is a \ref string_typet.
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
/// \param type Source type.
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
  range_typet(const mp_integer &_from, const mp_integer &_to)
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
/// \param type Source type.
/// \return True if \param type is a \ref range_typet.
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
/// \param type Source type.
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
/// element-wise on their operand vectors. Compared to \ref array_typet
/// that has no element-wise operators. Note that `remove_vector.h` removes
/// this data type by compilation into arrays.
class vector_typet:public type_with_subtypet
{
public:
  vector_typet(
    const typet &_subtype,
    const exprt &_size):type_with_subtypet(ID_vector, _subtype)
  {
    size()=_size;
  }

  const exprt &size() const
  {
    return static_cast<const exprt &>(find(ID_size));
  }

  exprt &size()
  {
    return static_cast<exprt &>(add(ID_size));
  }
};

/// Check whether a reference to a typet is a \ref vector_typet.
/// \param type Source type.
/// \return True if \param type is a \ref vector_typet.
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
/// \param type Source type.
/// \return Object of type \ref vector_typet.
inline const vector_typet &to_vector_type(const typet &type)
{
  PRECONDITION(can_cast_type<vector_typet>(type));
  return static_cast<const vector_typet &>(type);
}

/// \copydoc to_vector_type(const typet &)
inline vector_typet &to_vector_type(typet &type)
{
  PRECONDITION(can_cast_type<vector_typet>(type));
  return static_cast<vector_typet &>(type);
}

/// Complex numbers made of pair of given subtype
class complex_typet:public type_with_subtypet
{
public:
  complex_typet():type_with_subtypet(ID_complex)
  {
  }

  explicit complex_typet(const typet &_subtype):
    type_with_subtypet(ID_complex, _subtype)
  {
  }
};

/// Check whether a reference to a typet is a \ref complex_typet.
/// \param type Source type.
/// \return True if \param type is a \ref complex_typet.
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
/// \param type Source type.
/// \return Object of type \ref complex_typet.
inline const complex_typet &to_complex_type(const typet &type)
{
  PRECONDITION(can_cast_type<complex_typet>(type));
  return static_cast<const complex_typet &>(type);
}

/// \copydoc to_complex_type(const typet &)
inline complex_typet &to_complex_type(typet &type)
{
  PRECONDITION(can_cast_type<complex_typet>(type));
  return static_cast<complex_typet &>(type);
}

bool is_constant_or_has_constant_components(
  const typet &type,
  const namespacet &ns);

#endif // CPROVER_UTIL_STD_TYPES_H
