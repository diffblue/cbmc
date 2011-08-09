/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STD_EXPR_H
#define CPROVER_STD_EXPR_H

#include <assert.h>

#include <expr.h>
#include <std_types.h>

class transt:public exprt
{
public:
  inline transt()
  {
    id(ID_trans);
    operands().resize(3);
  }

  inline exprt &invar() { return op0(); }
  inline exprt &init()  { return op1(); }
  inline exprt &trans() { return op2(); }

  inline const exprt &invar() const { return op0(); }
  inline const exprt &init()  const { return op1(); }
  inline const exprt &trans() const { return op2(); }
};

extern inline const transt &to_trans(const exprt &expr)
{
  assert(expr.id()==ID_trans && expr.operands().size()==3);
  return static_cast<const transt &>(expr);
}

extern inline transt &to_trans(exprt &expr)
{
  assert(expr.id()==ID_trans && expr.operands().size()==3);
  return static_cast<transt &>(expr);
}

class symbol_exprt:public exprt
{
public:
  inline symbol_exprt():exprt(ID_symbol)
  {
  }

  inline explicit symbol_exprt(const irep_idt &identifier):exprt(ID_symbol)
  {
    set_identifier(identifier);
  }

  inline explicit symbol_exprt(const typet &type):exprt(ID_symbol, type)
  {
  }

  inline symbol_exprt(const irep_idt &identifier,
                      const typet &type):exprt(ID_symbol, type)
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

extern inline const symbol_exprt &to_symbol_expr(const exprt &expr)
{
  assert(expr.id()==ID_symbol && !expr.has_operands());
  return static_cast<const symbol_exprt &>(expr);
}

extern inline symbol_exprt &to_symbol_expr(exprt &expr)
{
  assert(expr.id()==ID_symbol && !expr.has_operands());
  return static_cast<symbol_exprt &>(expr);
}

class unary_exprt:public exprt
{
public:
  inline unary_exprt()
  {
    operands().resize(1);
  }

  inline explicit unary_exprt(const irep_idt &id):exprt(id)
  {
    operands().resize(1);
  }

  inline unary_exprt(
    const irep_idt &_id,
    const exprt &_op):
    exprt(_id, _op.type())
  {
    copy_to_operands(_op);
  }

  inline unary_exprt(
    const irep_idt &_id,
    const exprt &_op,
    const typet &_type):
    exprt(_id, _type)
  {
    copy_to_operands(_op);
  }
};

class unary_minus_exprt:public unary_exprt
{
public:
  inline unary_minus_exprt():unary_exprt(ID_unary_minus)
  {
  }

  inline unary_minus_exprt(
    const exprt &_op,
    const typet &_type):
    unary_exprt(ID_unary_minus, _op, _type)
  {
  }
};

class predicate_exprt:public exprt
{
public:
  inline predicate_exprt()
  {
    type()=typet(ID_bool);
  }

  inline predicate_exprt(const irep_idt &_id):exprt(_id, typet(ID_bool))
  {
  }

  inline predicate_exprt(
    const irep_idt &_id,
    const exprt &_op):exprt(_id, typet(ID_bool))
  {
    copy_to_operands(_op);
  }

  inline predicate_exprt(
    const irep_idt &_id,
    const exprt &_op0,
    const exprt &_op1):exprt(_id, typet(ID_bool))
  {
    copy_to_operands(_op0, _op1);
  }
};

class binary_relation_exprt:public predicate_exprt
{
public:
  inline binary_relation_exprt()
  {
    operands().resize(2);
  }

  inline explicit binary_relation_exprt(const irep_idt &id):predicate_exprt(id)
  {
    operands().resize(2);
  }

  inline binary_relation_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    const exprt &_rhs):
    predicate_exprt(_id, _lhs, _rhs)
  {
  }

  inline exprt &lhs()
  {
    return op0();
  }

  inline const exprt &lhs() const
  {
    return op0();
  }

  inline exprt &rhs()
  {
    return op1();
  }

  inline const exprt &rhs() const
  {
    return op1();
  }
};

class binary_exprt:public exprt
{
public:
  inline binary_exprt()
  {
    operands().resize(2);
  }

  inline explicit binary_exprt(const irep_idt &_id):exprt(_id)
  {
    operands().resize(2);
  }

  inline binary_exprt(
    const irep_idt &_id,
    const typet &_type):exprt(_id, _type)
  {
    operands().resize(2);
  }

  inline binary_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    const exprt &_rhs):
    exprt(_id, _lhs.type())
  {
    copy_to_operands(_lhs, _rhs);
  }

  inline binary_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    const exprt &_rhs,
    const typet &_type):
    exprt(_id, _type)
  {
    copy_to_operands(_lhs, _rhs);
  }
};

class plus_exprt:public binary_exprt
{
public:
  inline plus_exprt():binary_exprt(ID_plus)
  {
  }

  inline plus_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    binary_exprt(_lhs, ID_plus, _rhs)
  {
  }
};

class minus_exprt:public binary_exprt
{
public:
  inline minus_exprt():binary_exprt(ID_minus)
  {
  }

  inline minus_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    binary_exprt(_lhs, ID_minus, _rhs)
  {
  }
};

class mult_exprt:public binary_exprt
{
public:
  inline mult_exprt():binary_exprt(ID_mult)
  {
  }

  inline mult_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    binary_exprt(_lhs, ID_mult, _rhs)
  {
  }
};

extern inline const mult_exprt &to_mult_expr(const exprt &expr)
{
  assert(expr.id()==ID_mult && expr.operands().size()>=2);
  return static_cast<const mult_exprt &>(expr);
}

extern inline mult_exprt &to_mult_expr(exprt &expr)
{
  assert(expr.id()==ID_mult && expr.operands().size()>=2);
  return static_cast<mult_exprt &>(expr);
}

class div_exprt:public binary_exprt
{
public:
  inline div_exprt():binary_exprt(ID_div)
  {
  }

  inline div_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    binary_exprt(_lhs, ID_div, _rhs)
  {
  }
};

extern inline const div_exprt &to_div_expr(const exprt &expr)
{
  assert(expr.id()==ID_div && expr.operands().size()==2);
  return static_cast<const div_exprt &>(expr);
}

extern inline div_exprt &to_div_expr(exprt &expr)
{
  assert(expr.id()==ID_div && expr.operands().size()==2);
  return static_cast<div_exprt &>(expr);
}

class mod_exprt:public binary_exprt
{
public:
  inline mod_exprt():binary_exprt(ID_mod)
  {
  }

  inline mod_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    binary_exprt(_lhs, ID_mod, _rhs)
  {
  }
};

extern inline const mod_exprt &to_mod_expr(const exprt &expr)
{
  assert(expr.id()==ID_mod && expr.operands().size()==2);
  return static_cast<const mod_exprt &>(expr);
}

extern inline mod_exprt &to_mod_expr(exprt &expr)
{
  assert(expr.id()==ID_mod && expr.operands().size()==2);
  return static_cast<mod_exprt &>(expr);
}

// WILL GO AWAY

class equality_exprt:public binary_relation_exprt
{
public:
  inline equality_exprt():binary_relation_exprt(ID_equal)
  {
  }

  inline equality_exprt(const exprt &_lhs, const exprt &_rhs):
    binary_relation_exprt(_lhs, ID_equal, _rhs)
  {
  }
};

extern inline const equality_exprt &to_equality_expr(const exprt &expr)
{
  assert(expr.id()==ID_equal && expr.operands().size()==2);
  return static_cast<const equality_exprt &>(expr);
}

extern inline equality_exprt &to_equality_expr(exprt &expr)
{
  assert(expr.id()==ID_equal && expr.operands().size()==2);
  return static_cast<equality_exprt &>(expr);
}

// USE THIS ONE

class equal_exprt:public binary_relation_exprt
{
public:
  inline equal_exprt():binary_relation_exprt(ID_equal)
  {
  }

  inline equal_exprt(const exprt &_lhs, const exprt &_rhs):
    binary_relation_exprt(_lhs, ID_equal, _rhs)
  {
  }
};

extern inline const equal_exprt &to_equal_expr(const exprt &expr)
{
  assert(expr.id()==ID_equal && expr.operands().size()==2);
  return static_cast<const equal_exprt &>(expr);
}

extern inline equal_exprt &to_equal_expr(exprt &expr)
{
  assert(expr.id()==ID_equal && expr.operands().size()==2);
  return static_cast<equal_exprt &>(expr);
}

class index_exprt:public exprt
{
public:
  inline index_exprt():exprt(ID_index)
  {
    operands().resize(2);
  }
 
  explicit inline index_exprt(const typet &_type):exprt(ID_index, _type)
  {
    operands().resize(2);
  }
  
  inline index_exprt(const exprt &_array, const exprt &_index):
    exprt(ID_index, _array.type().subtype())
  {
    copy_to_operands(_array, _index);
  }
  
  inline index_exprt(
    const exprt &_array,
    const exprt &_index,
    const typet &_type):
    exprt(ID_index, _type)
  {
    copy_to_operands(_array, _index);
  }
  
  inline exprt &array()
  {
    return op0();
  }

  inline const exprt &array() const
  {
    return op0();
  }

  inline exprt &index()
  {
    return op1();
  }

  inline const exprt &index() const
  {
    return op1();
  }

  friend inline const index_exprt &to_index_expr(const exprt &expr)
  {
    assert(expr.id()==ID_index && expr.operands().size()==2);
    return static_cast<const index_exprt &>(expr);
  }

  friend inline index_exprt &to_index_expr(exprt &expr)
  {
    assert(expr.id()==ID_index && expr.operands().size()==2);
    return static_cast<index_exprt &>(expr);
  }
};

const index_exprt &to_index_expr(const exprt &expr);
index_exprt &to_index_expr(exprt &expr);

class array_of_exprt:public exprt
{
public:
  inline array_of_exprt():exprt(ID_array_of)
  {
    operands().resize(1);
  }
 
  explicit inline array_of_exprt(
    const exprt &_what, const typet &_type):exprt(ID_array_of)
  {
    operands().resize(1);
    op0()=_what;
    type()=_type;
  }
 
  inline exprt &what()
  {
    return op0();
  }

  inline const exprt &what() const
  {
    return op0();
  }

  friend inline const array_of_exprt &to_array_of_expr(const exprt &expr)
  {
    assert(expr.id()==ID_array_of && expr.operands().size()==1);
    return static_cast<const array_of_exprt &>(expr);
  }

  friend inline array_of_exprt &to_array_of_expr(exprt &expr)
  {
    assert(expr.id()==ID_array_of && expr.operands().size()==1);
    return static_cast<array_of_exprt &>(expr);
  }
};

const array_of_exprt &to_array_of_expr(const exprt &expr);
array_of_exprt &to_array_of_expr(exprt &expr);

class array_exprt:public exprt
{
public:
  inline array_exprt():exprt(ID_array)
  {
  }
 
  explicit inline array_exprt(const typet &_type):
    exprt(ID_array, _type)
  {
  }
 
  friend inline const array_exprt &to_array_expr(const exprt &expr)
  {
    assert(expr.id()==ID_array);
    return static_cast<const array_exprt &>(expr);
  }

  friend inline array_exprt &to_array_expr(exprt &expr)
  {
    assert(expr.id()==ID_array);
    return static_cast<array_exprt &>(expr);
  }
};

const array_exprt &to_array_expr(const exprt &expr);
array_exprt &to_array_expr(exprt &expr);

class union_exprt:public exprt
{
public:
  inline union_exprt():exprt(ID_union)
  {
    operands().resize(1);
  }
 
  explicit inline union_exprt(const typet &_type):
    exprt(ID_union, _type)
  {
    operands().resize(1);
  }
 
  friend inline const union_exprt &to_union_expr(const exprt &expr)
  {
    assert(expr.id()==ID_union && expr.operands().size()==1);
    return static_cast<const union_exprt &>(expr);
  }

  friend inline union_exprt &to_union_expr(exprt &expr)
  {
    assert(expr.id()==ID_union && expr.operands().size()==1);
    return static_cast<union_exprt &>(expr);
  }

  inline irep_idt get_component_name() const
  {
    return get(ID_component_name);
  }

  inline void set_component_name(const irep_idt &component_name)
  {
    set(ID_component_name, component_name);
  }
  
  inline unsigned get_component_number() const
  {
    return get_int(ID_component_number);
  }

  inline void set_component_number(unsigned component_number)
  {
    set(ID_component_number, component_number);
  }
  
  inline const exprt &op() const
  {
    return op0();
  }

  inline exprt &op()
  {
    return op0();
  }
};

const union_exprt &to_union_expr(const exprt &expr);
union_exprt &to_union_expr(exprt &expr);

class struct_exprt:public exprt
{
public:
  inline struct_exprt():exprt(ID_struct)
  {
  }
 
  explicit inline struct_exprt(const typet &_type):
    exprt(ID_struct, _type)
  {
  }
 
  friend inline const struct_exprt &to_struct_expr(const exprt &expr)
  {
    assert(expr.id()==ID_struct);
    return static_cast<const struct_exprt &>(expr);
  }

  friend inline struct_exprt &to_struct_expr(exprt &expr)
  {
    assert(expr.id()==ID_struct);
    return static_cast<struct_exprt &>(expr);
  }
};

const struct_exprt &to_struct_expr(const exprt &expr);
struct_exprt &to_struct_expr(exprt &expr);

class object_descriptor_exprt:public exprt
{
public:
  inline object_descriptor_exprt():exprt(ID_object_descriptor)
  {
    operands().resize(2);
    op0().id(ID_unknown);
    op1().id(ID_unknown);
  }

  inline exprt &object()
  {
    return op0();
  }

  inline const exprt &object() const
  {
    return op0();
  }
  
  const exprt &root_object() const
  {
    const exprt *p=&object();

    while(p->id()==ID_member || p->id()==ID_index)
    {
      assert(p->operands().size()!=0);
      p=&p->op0();
    }
    
    return *p;
  }

  inline exprt &offset()
  {
    return op1();
  }

  inline const exprt &offset() const
  {
    return op1();
  }

  friend inline const object_descriptor_exprt &to_object_descriptor_expr(const exprt &expr)
  {
    assert(expr.id()==ID_object_descriptor && expr.operands().size()==2);
    return static_cast<const object_descriptor_exprt &>(expr);
  }

  friend inline object_descriptor_exprt &to_object_descriptor_expr(exprt &expr)
  {
    assert(expr.id()==ID_object_descriptor && expr.operands().size()==2);
    return static_cast<object_descriptor_exprt &>(expr);
  }
};

const object_descriptor_exprt &to_object_descriptor_expr(const exprt &expr);
object_descriptor_exprt &to_object_descriptor_expr(exprt &expr);

class dynamic_object_exprt:public exprt
{
public:
  inline dynamic_object_exprt():exprt(ID_dynamic_object)
  {
    operands().resize(2);
    op0().id(ID_unknown);
    op1().id(ID_unknown);
  }

  inline explicit dynamic_object_exprt(const typet &type):exprt(ID_dynamic_object, type)
  {
    operands().resize(2);
    op0().id(ID_unknown);
    op1().id(ID_unknown);
  }

  inline exprt &instance()
  {
    return op0();
  }

  inline const exprt &instance() const
  {
    return op0();
  }

  inline exprt &valid()
  {
    return op1();
  }

  inline const exprt &valid() const
  {
    return op1();
  }

  friend inline const dynamic_object_exprt &to_dynamic_object_expr(const exprt &expr)
  {
    assert(expr.id()==ID_dynamic_object && expr.operands().size()==2);
    return static_cast<const dynamic_object_exprt &>(expr);
  }

  friend inline dynamic_object_exprt &to_dynamic_object_expr(exprt &expr)
  {
    assert(expr.id()==ID_dynamic_object && expr.operands().size()==2);
    return static_cast<dynamic_object_exprt &>(expr);
  }
};

const dynamic_object_exprt &to_dynamic_object_expr(const exprt &expr);
dynamic_object_exprt &to_dynamic_object_expr(exprt &expr);

class typecast_exprt:public exprt
{
public:
  inline explicit typecast_exprt(const typet &_type):exprt(ID_typecast, _type)
  {
    operands().resize(1);
  }

  inline typecast_exprt(const exprt &op, const typet &_type):exprt(ID_typecast, _type)
  {
    copy_to_operands(op);
  }

  inline exprt &op()
  {
    return op0();
  }

  inline const exprt &op() const
  {
    return op0();
  }
};

extern inline const typecast_exprt &to_typecast_expr(const exprt &expr)
{
  assert(expr.id()==ID_typecast && expr.operands().size()==1);
  return static_cast<const typecast_exprt &>(expr);
}

extern inline typecast_exprt &to_typecast_expr(exprt &expr)
{
  assert(expr.id()==ID_typecast && expr.operands().size()==1);
  return static_cast<typecast_exprt &>(expr);
}

class and_exprt:public exprt
{
public:
  inline and_exprt():exprt(ID_and, bool_typet())
  {
  }

  inline and_exprt(const exprt &op0, const exprt &op1):exprt(ID_and, typet(ID_bool))
  {
    copy_to_operands(op0, op1);
  }

  and_exprt(const exprt::operandst &op):exprt(ID_and, bool_typet())
  {
    if(op.empty())
      make_true();
    else if(op.size()==1)
      *this=static_cast<const and_exprt &>(op.front());
    else
      operands()=op;
  }
};

class implies_exprt:public exprt
{
public:
  inline implies_exprt():exprt(ID_implies, bool_typet())
  {
    operands().resize(2);
  }

  inline implies_exprt(const exprt &op0, const exprt &op1):
    exprt(ID_implies, bool_typet())
  {
    copy_to_operands(op0, op1);
  }
};

class or_exprt:public exprt
{
public:
  inline or_exprt():exprt(ID_or, typet(ID_bool))
  {
  }

  inline or_exprt(const exprt &op0, const exprt &op1):exprt(ID_or, bool_typet())
  {
    copy_to_operands(op0, op1);
  }

  or_exprt(const exprt::operandst &op):exprt(ID_or, bool_typet())
  {
    if(op.empty())
      make_false();
    else if(op.size()==1)
      *this=static_cast<const or_exprt &>(op.front());
    else
      operands()=op;
  }
};

class bitnot_exprt:public unary_exprt
{
public:
  inline bitnot_exprt():unary_exprt(ID_bitnot)
  {
  }

  explicit inline bitnot_exprt(const exprt &op):unary_exprt(ID_bitnot, op)
  {
  }
};

class bitor_exprt:public exprt
{
public:
  inline bitor_exprt():exprt(ID_bitor)
  {
  }

  inline bitor_exprt(const exprt &op0, const exprt &op1):exprt(ID_bitor, op0.type())
  {
    copy_to_operands(op0, op1);
  }
};

class bitxor_exprt:public exprt
{
public:
  inline bitxor_exprt():exprt(ID_bitxor)
  {
  }

  inline bitxor_exprt(const exprt &op0, const exprt &op1):exprt(ID_bitxor, op0.type())
  {
    copy_to_operands(op0, op1);
  }
};

class bitand_exprt:public exprt
{
public:
  inline bitand_exprt():exprt(ID_bitand)
  {
  }

  inline bitand_exprt(const exprt &op0, const exprt &op1):exprt(ID_bitand, op0.type())
  {
    copy_to_operands(op0, op1);
  }
};

class shift_exprt:public binary_exprt
{
public:
  explicit inline shift_exprt(const irep_idt &_id):binary_exprt(_id)
  {
  }

  inline shift_exprt(const irep_idt &_id, const typet &_type):binary_exprt(_id, _type)
  {
  }

  inline shift_exprt(const exprt &_src, const irep_idt &_id, const exprt &_distance):
    binary_exprt(_src, _id, _distance)
  {
  }

  inline exprt &distance()
  {
    return op1();
  }

  inline const exprt &distance() const
  {
    return op1();
  }
};

class shl_exprt:public shift_exprt
{
public:
  inline shl_exprt():shift_exprt(ID_shl)
  {
  }

  inline shl_exprt(const exprt &_src, const exprt &_distance):shift_exprt(_src, ID_shl, _distance)
  {
  }
  
  inline exprt &distance()
  {
    return op1();
  }

  inline const exprt &distance() const
  {
    return op1();
  }
};

class ashr_exprt:public shift_exprt
{
public:
  inline ashr_exprt():shift_exprt(ID_shl)
  {
  }

  inline ashr_exprt(const exprt &_src, const exprt &_distance):shift_exprt(_src, ID_ashr, _distance)
  {
  }
  
  inline exprt &distance()
  {
    return op1();
  }

  inline const exprt &distance() const
  {
    return op1();
  }
};

class lshr_exprt:public shift_exprt
{
public:
  inline lshr_exprt():shift_exprt(ID_shl)
  {
  }

  inline lshr_exprt(const exprt &_src, const exprt &_distance):shift_exprt(_src, ID_lshr, _distance)
  {
  }
  
  inline exprt &distance()
  {
    return op1();
  }

  inline const exprt &distance() const
  {
    return op1();
  }
};

class extractbit_exprt:public exprt
{
public:
  inline extractbit_exprt():exprt(ID_extractbit)
  {
    operands().resize(2);
  }

  inline extractbit_exprt(
    const exprt &_src,
    const exprt &_index):exprt(ID_extractbit, bool_typet())
  {
    copy_to_operands(_src, _index);
  }

  exprt &src()
  {
    return op0();
  }

  exprt &index()
  {
    return op1();
  }

  const exprt &src() const
  {
    return op0();
  }

  const exprt &index() const
  {
    return op1();
  }
};

extern inline const extractbit_exprt &to_extractbit_expr(const exprt &expr)
{
  assert(expr.id()==ID_extractbit && expr.operands().size()==2);
  return static_cast<const extractbit_exprt &>(expr);
}

extern inline extractbit_exprt &to_extractbit_expr(exprt &expr)
{
  assert(expr.id()==ID_extractbit && expr.operands().size()==2);
  return static_cast<extractbit_exprt &>(expr);
}

class extractbits_exprt:public exprt
{
public:
  inline extractbits_exprt():exprt(ID_extractbits)
  {
    operands().resize(3);
  }

  // the ordering upper-lower matches the SMT-LIB
  inline extractbits_exprt(
    const exprt &_src,
    const exprt &_upper,
    const exprt &_lower,
    const typet &_type):exprt(ID_extractbits, _type)
  {
    copy_to_operands(_src, _lower, _upper);
  }
  
  exprt &src()
  {
    return op0();
  }

  exprt &upper()
  {
    return op1();
  }

  exprt &lower()
  {
    return op2();
  }

  const exprt &src() const
  {
    return op0();
  }

  const exprt &upper() const
  {
    return op1();
  }

  const exprt &lower() const
  {
    return op2();
  }

};

extern inline const extractbits_exprt &to_extractbits_expr(const exprt &expr)
{
  assert(expr.id()==ID_extractbits && expr.operands().size()==3);
  return static_cast<const extractbits_exprt &>(expr);
}

extern inline extractbits_exprt &to_extractbits_expr(exprt &expr)
{
  assert(expr.id()==ID_extractbits && expr.operands().size()==3);
  return static_cast<extractbits_exprt &>(expr);
}

class address_of_exprt:public exprt
{
public:
  explicit address_of_exprt(const exprt &op):
    exprt(ID_address_of, pointer_typet())
  {
    type().subtype()=op.type();
    copy_to_operands(op);
  }

  explicit address_of_exprt():
    exprt(ID_address_of, pointer_typet())
  {
    operands().resize(1);
  }
  
  inline exprt &object()
  {
    return op0();
  }

  inline const exprt &object() const
  {
    return op0();
  }
};

extern inline const address_of_exprt &to_address_of_expr(const exprt &expr)
{
  assert(expr.id()==ID_address_of && expr.operands().size()==1);
  return static_cast<const address_of_exprt &>(expr);
}

extern inline address_of_exprt &to_address_of_expr(exprt &expr)
{
  assert(expr.id()==ID_address_of && expr.operands().size()==1);
  return static_cast<address_of_exprt &>(expr);
}

class not_exprt:public exprt
{
public:
  inline explicit not_exprt(const exprt &op):exprt(ID_not, bool_typet())
  {
    copy_to_operands(op);
  }

  inline not_exprt():exprt(ID_not, bool_typet())
  {
    operands().resize(1);
  }
};

class dereference_exprt:public exprt
{
public:
  inline explicit dereference_exprt(const typet &type):exprt(ID_dereference, type)
  {
    operands().resize(1);
  }

  inline explicit dereference_exprt(const exprt &op):exprt(ID_dereference)
  {
    copy_to_operands(op);
  }

  inline dereference_exprt(const exprt &op, const typet &type):exprt(ID_dereference, type)
  {
    copy_to_operands(op);
  }

  inline dereference_exprt():exprt(ID_dereference)
  {
    operands().resize(1);
  }

  inline exprt &pointer()
  {
    return op0();
  }

  inline const exprt &pointer() const
  {
    return op0();
  }
};

extern inline const dereference_exprt &to_dereference_expr(const exprt &expr)
{
  assert(expr.id()==ID_dereference && expr.operands().size()==1);
  return static_cast<const dereference_exprt &>(expr);
}

extern inline dereference_exprt &to_dereference_expr(exprt &expr)
{
  assert(expr.id()==ID_dereference && expr.operands().size()==1);
  return static_cast<dereference_exprt &>(expr);
}

class if_exprt:public exprt
{
public:
  if_exprt(const exprt &cond, const exprt &t, const exprt &f):
    exprt(ID_if, t.type())
  {
    copy_to_operands(cond, t, f);
  }

  inline if_exprt():exprt(ID_if)
  {
    operands().resize(3);
  }
  
  inline exprt &cond()
  {
    return op0();
  }

  inline const exprt &cond() const
  {
    return op0();
  }

  inline exprt &true_case()
  {
    return op1();
  }

  inline const exprt &true_case() const
  {
    return op1();
  }

  inline exprt &false_case()
  {
    return op2();
  }

  inline const exprt &false_case() const
  {
    return op2();
  }
};

extern inline const if_exprt &to_if_expr(const exprt &expr)
{
  assert(expr.id()==ID_if && expr.operands().size()==3);
  return static_cast<const if_exprt &>(expr);
}

extern inline if_exprt &to_if_expr(exprt &expr)
{
  assert(expr.id()==ID_if && expr.operands().size()==3);
  return static_cast<if_exprt &>(expr);
}

class with_exprt:public exprt
{
public:
  with_exprt(
    const exprt &_old,
    const exprt &_where,
    const exprt &_new_value):
    exprt(ID_with, _old.type())
  {
    copy_to_operands(_old, _where, _new_value);
  }

  inline with_exprt():exprt(ID_with)
  {
    operands().resize(3);
  }
  
  inline exprt &old()
  {
    return op0();
  }

  inline const exprt &old() const
  {
    return op0();
  }

  inline exprt &where()
  {
    return op1();
  }

  inline const exprt &where() const
  {
    return op1();
  }

  inline exprt &new_value()
  {
    return op2();
  }

  inline const exprt &new_value() const
  {
    return op2();
  }
};

extern inline const with_exprt &to_with_expr(const exprt &expr)
{
  assert(expr.id()==ID_with && expr.operands().size()==3);
  return static_cast<const with_exprt &>(expr);
}

extern inline with_exprt &to_with_expr(exprt &expr)
{
  assert(expr.id()==ID_with && expr.operands().size()==3);
  return static_cast<with_exprt &>(expr);
}

class array_update_exprt:public exprt
{
public:
  array_update_exprt(
    const exprt &_array,
    const exprt &_index,
    const exprt &_new_value):
    exprt(ID_array_update, _array.type())
  {
    copy_to_operands(_array, _index, _new_value);
  }

  inline array_update_exprt():exprt(ID_array_update)
  {
    operands().resize(3);
  }
  
  inline exprt &array()
  {
    return op0();
  }

  inline const exprt &array() const
  {
    return op0();
  }

  inline exprt &index()
  {
    return op1();
  }

  inline const exprt &index() const
  {
    return op1();
  }

  inline exprt &new_value()
  {
    return op2();
  }

  inline const exprt &new_value() const
  {
    return op2();
  }
};

extern inline const array_update_exprt &to_array_update_expr(const exprt &expr)
{
  assert(expr.id()==ID_array_update && expr.operands().size()==3);
  return static_cast<const array_update_exprt &>(expr);
}

extern inline array_update_exprt &to_array_update_expr(exprt &expr)
{
  assert(expr.id()==ID_array_update && expr.operands().size()==3);
  return static_cast<array_update_exprt &>(expr);
}

class member_exprt:public exprt
{
public:
  inline explicit member_exprt(const exprt &op):exprt(ID_member)
  {
    copy_to_operands(op);
  }

  inline explicit member_exprt(const typet &_type):exprt(ID_member, _type)
  {
    operands().resize(1);
  }

  inline member_exprt(const exprt &op, const irep_idt &component_name):exprt(ID_member)
  {
    copy_to_operands(op);
    set_component_name(component_name);
  }

  inline member_exprt(const exprt &op, const irep_idt &component_name, const typet &_type):exprt(ID_member, _type)
  {
    copy_to_operands(op);
    set_component_name(component_name);
  }

  inline member_exprt():exprt(ID_member)
  {
    operands().resize(1);
  }
  
  inline irep_idt get_component_name() const
  {
    return get(ID_component_name);
  }

  inline void set_component_name(const irep_idt &component_name)
  {
    set(ID_component_name, component_name);
  }
  
  inline unsigned get_component_number() const
  {
    return get_int(ID_component_number);
  }

  inline void set_component_number(unsigned component_number)
  {
    set(ID_component_number, component_number);
  }
  
  inline const exprt &struct_op() const
  {
    return op0();
  }

  inline exprt &struct_op()
  {
    return op0();
  }
};

inline const member_exprt &to_member_expr(const exprt &expr)
{
  assert(expr.id()==ID_member);
  return static_cast<const member_exprt &>(expr);
}

inline member_exprt &to_member_expr(exprt &expr)
{
  assert(expr.id()==ID_member);
  return static_cast<member_exprt &>(expr);
}

class isnan_exprt:public predicate_exprt
{
public:
  inline explicit isnan_exprt(const exprt &op):
    predicate_exprt(ID_isnan, op)
  {
  }

  inline isnan_exprt():predicate_exprt(ID_isnan)
  {
    operands().resize(1);
  }
};

class ieee_float_equal_exprt:public binary_relation_exprt
{
public:
  inline ieee_float_equal_exprt():binary_relation_exprt(ID_ieee_float_equal)
  {
  }

  inline ieee_float_equal_exprt(const exprt &_lhs, const exprt &_rhs):
    binary_relation_exprt(_lhs, ID_ieee_float_equal, _rhs)
  {
  }
};

class type_exprt:public exprt
{
public:
  inline type_exprt():exprt(ID_type)
  {
  }

  inline explicit type_exprt(const typet &type):exprt(ID_type, type)
  {
  }
};

class constant_exprt:public exprt
{
public:
  inline constant_exprt():exprt(ID_constant)
  {
  }

  inline explicit constant_exprt(const typet &type):exprt(ID_constant, type)
  {
  }
  
  inline const irep_idt &get_value() const
  {
    return get(ID_value);
  }

  inline void set_value(const irep_idt &value)
  {
    set(ID_value, value);
  }
};

inline const constant_exprt &to_constant_expr(const exprt &expr)
{
  assert(expr.id()==ID_constant);
  return static_cast<const constant_exprt &>(expr);
}

inline constant_exprt &to_constant_expr(exprt &expr)
{
  assert(expr.id()==ID_constant);
  return static_cast<constant_exprt &>(expr);
}

class true_exprt:public constant_exprt
{
public:
  inline true_exprt():constant_exprt(bool_typet())
  {
    set_value(ID_true);
  }
};

class false_exprt:public constant_exprt
{
public:
  inline false_exprt():constant_exprt(bool_typet())
  {
    set_value(ID_false);
  }
};

class nil_exprt:public exprt
{
public:
  inline nil_exprt():exprt(static_cast<const exprt &>(get_nil_irep()))
  {
  }
};

class null_pointer_exprt:public constant_exprt
{
public:
  explicit null_pointer_exprt(const pointer_typet &type):constant_exprt(type)
  {
    set_value(ID_NULL);
  }
};

class function_application_exprt:public exprt
{
public:
  function_application_exprt():exprt(ID_function_application)
  {
    operands().resize(2);
  }

  exprt &function()
  {
    return op0();
  }

  const exprt &function() const
  {
    return op0();
  }

  typedef exprt::operandst argumentst;

  argumentst &arguments()
  {
    return op1().operands();
  }

  const argumentst &arguments() const
  {
    return op1().operands();
  }

  friend inline const function_application_exprt &to_function_application_expr(const exprt &expr)
  {
    assert(expr.id()==ID_function_application && expr.operands().size()==2);
    return static_cast<const function_application_exprt &>(expr);
  }

  friend inline function_application_exprt &to_function_application_expr(exprt &expr)
  {
    assert(expr.id()==ID_function_application && expr.operands().size()==2);
    return static_cast<function_application_exprt &>(expr);
  }
};

const function_application_exprt &to_function_application_expr(const exprt &expr);
function_application_exprt &to_function_application_expr(exprt &expr);

class concatenation_exprt:public exprt
{
public:
  concatenation_exprt():exprt(ID_concatenation)
  {
  }

  concatenation_exprt(const typet &_type):exprt(ID_concatenation, _type)
  {
  }

  friend inline const concatenation_exprt &to_concatenation_expr(const exprt &expr)
  {
    assert(expr.id()==ID_concatenation);
    return static_cast<const concatenation_exprt &>(expr);
  }

  friend inline concatenation_exprt &to_concatenation_expr(exprt &expr)
  {
    assert(expr.id()==ID_concatenation);
    return static_cast<concatenation_exprt &>(expr);
  }
};

const concatenation_exprt &to_concatenation_expr(const exprt &expr);
concatenation_exprt &to_concatenation_expr(exprt &expr);

class same_object_exprt:public exprt
{
public:
  same_object_exprt(const exprt &obj1, const exprt &obj2):
    exprt("same-object", bool_typet())
  {
    copy_to_operands(obj1, obj2);
  }
};

class sideeffect_exprt:public exprt
{
public:
  sideeffect_exprt(
    const irep_idt &_statement,
    const typet &type):exprt(ID_sideeffect, type)
  {
    set(ID_statement, _statement);
  }
};

class nondet_exprt:public sideeffect_exprt
{
public:
  explicit nondet_exprt(const typet &_type):sideeffect_exprt(ID_nondet, _type)
  {
  }
};

#endif
