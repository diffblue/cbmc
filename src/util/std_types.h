/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STD_TYPES_H
#define CPROVER_STD_TYPES_H

#include <assert.h>

#include <type.h>
#include <expr.h>
#include <mp_arith.h>

class bool_typet:public typet
{
public:
  inline bool_typet():typet(ID_bool)
  {
  }
};

class empty_typet:public typet
{
public:
  inline empty_typet():typet(ID_empty)
  {
  }
};

class integer_typet:public typet
{
public:
  inline integer_typet():typet(ID_integer)
  {
  }
};

class rational_typet:public typet
{
public:
  inline rational_typet():typet(ID_rational)
  {
  }
};

class real_typet:public typet
{
public:
  inline real_typet():typet(ID_real)
  {
  }
};

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

extern inline const symbol_typet &to_symbol_type(const typet &type)
{
  assert(type.id()==ID_symbol);
  return static_cast<const symbol_typet &>(type);
}

extern inline symbol_typet &to_symbol_type(typet &type)
{
  assert(type.id()==ID_symbol);
  return static_cast<symbol_typet &>(type);
}

// structs

class struct_union_typet:public typet
{
public:
  inline explicit struct_union_typet(const irep_idt &_id):typet(_id)
  {
  }

  class componentt:public exprt
  {
  public:
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
};

extern inline const struct_union_typet &to_struct_union_type(const typet &type)
{
  assert(type.id()==ID_struct ||
         type.id()==ID_union ||
         type.id()==ID_class);
  return static_cast<const struct_union_typet &>(type);
}

extern inline struct_union_typet &to_struct_union_type(typet &type)
{
  assert(type.id()==ID_struct ||
         type.id()==ID_union ||
         type.id()==ID_class);
  return static_cast<struct_union_typet &>(type);
}

class struct_typet:public struct_union_typet
{
public:
  struct_typet():struct_union_typet(ID_struct)
  {
  }
    
  bool is_prefix_of(const struct_typet &other) const;
};

extern inline const struct_typet &to_struct_type(const typet &type)
{
  assert(type.id()==ID_struct ||
         type.id()==ID_union ||
         type.id()==ID_class);
  return static_cast<const struct_typet &>(type);
}

extern inline struct_typet &to_struct_type(typet &type)
{
  assert(type.id()==ID_struct ||
         type.id()==ID_union ||
         type.id()==ID_class);
  return static_cast<struct_typet &>(type);
}

class union_typet:public struct_union_typet
{
public:
  union_typet():struct_union_typet(ID_union)
  {
  }
};

extern inline const union_typet &to_union_type(const typet &type)
{
  assert(type.id()==ID_union);
  return static_cast<const union_typet &>(type);
}

extern inline union_typet &to_union_type(typet &type)
{
  assert(type.id()==ID_union);
  return static_cast<union_typet &>(type);
}

// functions

class code_typet:public typet
{
public:
  inline code_typet():typet(ID_code)
  {
  }
  
  class argumentt:public exprt
  {
  public:
    inline argumentt():exprt(ID_argument)
    {
    }
    
    inline argumentt(const typet &type):exprt(ID_argument, type)
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
    return find(ID_arguments).get_bool(ID_ellipsis);
  }

  inline void make_ellipsis()
  {
    add(ID_arguments).set(ID_ellipsis, true);
  }

  typedef std::vector<argumentt> argumentst;

  inline const typet &return_type() const
  {
    return find_type(ID_return_type);
  }

  inline typet &return_type()
  {
    return add_type(ID_return_type);
  }

  inline const argumentst &arguments() const
  {
    return (const argumentst &)find(ID_arguments).get_sub();
  }

  inline argumentst &arguments()
  {
    return (argumentst &)add(ID_arguments).get_sub();
  }
  
  inline bool get_inlined() const
  {
    return get_bool(ID_C_inlined);
  }

  inline void set_inlined(bool value)
  {
    set(ID_C_inlined, value);
  }
};

extern inline const code_typet &to_code_type(const typet &type)
{
  assert(type.id()==ID_code);
  return static_cast<const code_typet &>(type);
}

extern inline code_typet &to_code_type(typet &type)
{
  assert(type.id()==ID_code);
  return static_cast<code_typet &>(type);
}

class array_typet:public typet
{
public:
  inline array_typet():typet(ID_array)
  {
  }
  
  inline array_typet(const typet &_subtype,
                     const exprt &_size):typet(ID_array)
  {
    size()=_size;
    subtype()=_subtype;
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

extern inline const array_typet &to_array_type(const typet &type)
{
  assert(type.id()==ID_array);
  return static_cast<const array_typet &>(type);
}

extern inline array_typet &to_array_type(typet &type)
{
  assert(type.id()==ID_array);
  return static_cast<array_typet &>(type);
}

// generic base class
class bitvector_typet:public typet
{
public:
  inline explicit bitvector_typet(const irep_idt &_id):typet(_id)
  {
  }

  unsigned get_width() const;

  inline void set_width(unsigned width)
  {
    set(ID_width, width);
  }
};

inline const bitvector_typet &to_bitvector_type(const typet &type)
{
  return static_cast<const bitvector_typet &>(type);
}

class pointer_typet:public bitvector_typet
{
public:
  inline pointer_typet():bitvector_typet(ID_pointer)
  {
  }

  inline explicit pointer_typet(const typet &_subtype):bitvector_typet(ID_pointer)
  {
    subtype()=_subtype;
  }

  inline explicit pointer_typet(const typet &_subtype, unsigned width):
    bitvector_typet(ID_pointer)
  {
    subtype()=_subtype;
    set_width(width);
  }
};

extern inline const pointer_typet &to_pointer_type(const typet &type)
{
  assert(type.id()==ID_pointer);
  return static_cast<const pointer_typet &>(type);
}

extern inline pointer_typet &to_pointer_type(typet &type)
{
  assert(type.id()==ID_pointer);
  return static_cast<pointer_typet &>(type);
}

class reference_typet:public pointer_typet
{
public:
  reference_typet()
  {
    set(ID_C_reference, true);
  }
};

bool is_reference(const typet &type);
bool is_rvalue_reference(const typet &type);

class bv_typet:public bitvector_typet
{
public:
  bv_typet():bitvector_typet(ID_bv)
  {
  }

  explicit bv_typet(unsigned width):bitvector_typet(ID_bv)
  {
    set_width(width);
  }
};

inline const bv_typet &to_bv_type(const typet &type)
{
  assert(type.id()==ID_bv);
  return static_cast<const bv_typet &>(type);
}

inline bv_typet &to_bv_type(typet &type)
{
  assert(type.id()==ID_bv);
  return static_cast<bv_typet &>(type);
}

class unsignedbv_typet:public bitvector_typet
{
public:
  unsignedbv_typet():bitvector_typet(ID_unsignedbv)
  {
  }

  explicit unsignedbv_typet(unsigned width):bitvector_typet(ID_unsignedbv)
  {
    set_width(width);
  }
};

inline const unsignedbv_typet &to_unsignedbv_type(const typet &type)
{
  assert(type.id()==ID_unsignedbv);
  return static_cast<const unsignedbv_typet &>(type);
}

inline unsignedbv_typet &to_unsignedbv_type(typet &type)
{
  assert(type.id()==ID_unsignedbv);
  return static_cast<unsignedbv_typet &>(type);
}

class signedbv_typet:public bitvector_typet
{
public:
  signedbv_typet():bitvector_typet(ID_signedbv)
  {
  }

  explicit signedbv_typet(unsigned width):bitvector_typet(ID_signedbv)
  {
    set_width(width);
  }
};

inline const signedbv_typet &to_signedbv_type(const typet &type)
{
  assert(type.id()==ID_signedbv);
  return static_cast<const signedbv_typet &>(type);
}

inline signedbv_typet &to_signedbv_type(typet &type)
{
  assert(type.id()==ID_signedbv);
  return static_cast<signedbv_typet &>(type);
}

class fixedbv_typet:public bitvector_typet
{
public:
  fixedbv_typet():bitvector_typet(ID_fixedbv)
  {
  }

  unsigned get_fraction_bits() const
  {
    return get_width()-get_integer_bits();
  }

  unsigned get_integer_bits() const;

  void set_integer_bits(unsigned b)
  {
    set(ID_integer_bits, b);
  }

  friend const fixedbv_typet &to_fixedbv_type(const typet &type)
  {
    assert(type.id()==ID_fixedbv);
    return static_cast<const fixedbv_typet &>(type);
  }
};

const fixedbv_typet &to_fixedbv_type(const typet &type);

class floatbv_typet:public bitvector_typet
{
public:
  floatbv_typet():bitvector_typet(ID_floatbv)
  {
  }

  unsigned get_e() const
  {
    return get_width()-get_f();
  }

  unsigned get_f() const;

  void set_f(unsigned b)
  {
    set(ID_f, b);
  }

  friend const floatbv_typet &to_floatbv_type(const typet &type)
  {
    assert(type.id()==ID_floatbv);
    return static_cast<const floatbv_typet &>(type);
  }
};

const floatbv_typet &to_floatbv_type(const typet &type);

class string_typet:public typet
{
public:
  string_typet():typet(ID_string)
  {
  }

  friend const string_typet &to_string_type(const typet &type)
  {
    assert(type.id()==ID_string);
    return static_cast<const string_typet &>(type);
  }
};

const string_typet &to_string_type(const typet &type);

class range_typet:public typet
{
public:
  range_typet():typet(ID_range)
  {
  }

  friend const range_typet &to_range_type(const typet &type)
  {
    assert(type.id()==ID_range);
    return static_cast<const range_typet &>(type);
  }

  mp_integer get_from() const;
  mp_integer get_to() const;

  void set_from(const mp_integer &_from);
  void set_to(const mp_integer &to);
};

const range_typet &to_range_type(const typet &type);

class vector_typet:public typet
{
public:
  vector_typet():typet(ID_vector)
  {
  }
  
  vector_typet(const typet &_subtype,
               const exprt &_size):typet(ID_vector)
  {
    size()=_size;
    subtype()=_subtype;
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

extern inline const vector_typet &to_vector_type(const typet &type)
{
  assert(type.id()==ID_vector);
  return static_cast<const vector_typet &>(type);
}

extern inline vector_typet &to_vector_type(typet &type)
{
  assert(type.id()==ID_vector);
  return static_cast<vector_typet &>(type);
}

#endif
