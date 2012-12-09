/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STD_EXPR_H
#define CPROVER_STD_EXPR_H

/*! \file util/std_expr.h
 * \brief API to expression classes
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

#include <cassert>

#include <std_types.h>

/*! \defgroup gr_std_expr Conversion to specific expressions
 *  Conversion to subclasses of @ref exprt
*/

/*! \brief A transition system, consisting of
           state invariant, initial state predicate,
           and transition predicate
*/
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

/*! \brief Cast a generic exprt to a \ref transt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * transt.
 *
 * \param expr Source expression
 * \return Object of type \ref transt
 *
 * \ingroup gr_std_expr
*/
extern inline const transt &to_trans_expr(const exprt &expr)
{
  assert(expr.id()==ID_trans && expr.operands().size()==3);
  return static_cast<const transt &>(expr);
}

/*! \copydoc to_trans(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline transt &to_trans_expr(exprt &expr)
{
  assert(expr.id()==ID_trans && expr.operands().size()==3);
  return static_cast<transt &>(expr);
}

/*! \brief Expression to hold a symbol (variable)
*/
class symbol_exprt:public exprt
{
public:
  inline symbol_exprt():exprt(ID_symbol)
  {
  }

  /*! \brief Constructor 
   * \param identifier Name of symbol
  */
  inline explicit symbol_exprt(const irep_idt &identifier):exprt(ID_symbol)
  {
    set_identifier(identifier);
  }

  /*! \brief Constructor 
   * \param  type Type of symbol
  */
  inline explicit symbol_exprt(const typet &type):exprt(ID_symbol, type)
  {
  }

  /*! \brief Constructor 
   * \param identifier Name of symbol
   * \param  type Type of symbol
  */
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

/*! \brief Cast a generic exprt to a \ref symbol_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * symbol_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref symbol_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const symbol_exprt &to_symbol_expr(const exprt &expr)
{
  assert(expr.id()==ID_symbol && !expr.has_operands());
  return static_cast<const symbol_exprt &>(expr);
}

/*! \copydoc to_symbol_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline symbol_exprt &to_symbol_expr(exprt &expr)
{
  assert(expr.id()==ID_symbol && !expr.has_operands());
  return static_cast<symbol_exprt &>(expr);
}

/*! \brief Generic base class for unary expressions
*/
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

/*! \brief The unary minus expression
*/
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

/*! \brief A generic base class for expressions that are predicates
*/
class predicate_exprt:public exprt
{
public:
  inline predicate_exprt()
  {
    type()=typet(ID_bool);
  }

  explicit inline predicate_exprt(const irep_idt &_id):
    exprt(_id, typet(ID_bool))
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

/*! \brief A generic base class for relations, i.e., binary predicates
*/
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

/*! \brief A generic base class for binary expressions
*/
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

/*! \brief The plus expression
*/
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

  inline plus_exprt(
    const exprt &_lhs,
    const exprt &_rhs,
    const typet &_type):
    binary_exprt(_lhs, ID_plus, _rhs, _type)
  {
  }
};

/*! \brief Cast a generic exprt to a \ref plus_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * plus_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref plus_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const plus_exprt &to_plus_expr(const exprt &expr)
{
  assert(expr.id()==ID_plus && expr.operands().size()>=2);
  return static_cast<const plus_exprt &>(expr);
}

/*! \copydoc to_plus_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline plus_exprt &to_plus_expr(exprt &expr)
{
  assert(expr.id()==ID_plus && expr.operands().size()>=2);
  return static_cast<plus_exprt &>(expr);
}

/*! \brief binary minus
*/
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

/*! \brief Cast a generic exprt to a \ref minus_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * minus_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref minus_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const minus_exprt &to_minus_expr(const exprt &expr)
{
  assert(expr.id()==ID_minus && expr.operands().size()>=2);
  return static_cast<const minus_exprt &>(expr);
}

/*! \copydoc to_minus_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline minus_exprt &to_minus_expr(exprt &expr)
{
  assert(expr.id()==ID_minus && expr.operands().size()>=2);
  return static_cast<minus_exprt &>(expr);
}

/*! \brief binary multiplication
*/
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

/*! \brief Cast a generic exprt to a \ref mult_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * mult_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref mult_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const mult_exprt &to_mult_expr(const exprt &expr)
{
  assert(expr.id()==ID_mult && expr.operands().size()>=2);
  return static_cast<const mult_exprt &>(expr);
}

/*! \copydoc to_mult_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline mult_exprt &to_mult_expr(exprt &expr)
{
  assert(expr.id()==ID_mult && expr.operands().size()>=2);
  return static_cast<mult_exprt &>(expr);
}

/*! \brief division (integer and real)
*/
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

/*! \brief Cast a generic exprt to a \ref div_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * div_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref div_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const div_exprt &to_div_expr(const exprt &expr)
{
  assert(expr.id()==ID_div && expr.operands().size()==2);
  return static_cast<const div_exprt &>(expr);
}

/*! \copydoc to_div_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline div_exprt &to_div_expr(exprt &expr)
{
  assert(expr.id()==ID_div && expr.operands().size()==2);
  return static_cast<div_exprt &>(expr);
}

/*! \brief binary modulo
*/
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

/*! \brief Cast a generic exprt to a \ref mod_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * mod_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref mod_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const mod_exprt &to_mod_expr(const exprt &expr)
{
  assert(expr.id()==ID_mod && expr.operands().size()==2);
  return static_cast<const mod_exprt &>(expr);
}

/*! \copydoc to_mod_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline mod_exprt &to_mod_expr(exprt &expr)
{
  assert(expr.id()==ID_mod && expr.operands().size()==2);
  return static_cast<mod_exprt &>(expr);
}

/*! \brief equality
*/
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

/*! \brief Cast a generic exprt to an \ref equal_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * equal_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref equal_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const equal_exprt &to_equal_expr(const exprt &expr)
{
  assert(expr.id()==ID_equal && expr.operands().size()==2);
  return static_cast<const equal_exprt &>(expr);
}

/*! \copydoc to_equal_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline equal_exprt &to_equal_expr(exprt &expr)
{
  assert(expr.id()==ID_equal && expr.operands().size()==2);
  return static_cast<equal_exprt &>(expr);
}

/*! \brief inequality
*/
class notequal_exprt:public binary_relation_exprt
{
public:
  inline notequal_exprt():binary_relation_exprt(ID_notequal)
  {
  }

  inline notequal_exprt(const exprt &_lhs, const exprt &_rhs):
    binary_relation_exprt(_lhs, ID_notequal, _rhs)
  {
  }
};

/*! \brief Cast a generic exprt to an \ref notequal_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * notequal_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref notequal_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const notequal_exprt &to_notequal_expr(const exprt &expr)
{
  assert(expr.id()==ID_notequal && expr.operands().size()==2);
  return static_cast<const notequal_exprt &>(expr);
}

/*! \copydoc to_notequal_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline notequal_exprt &to_notequal_expr(exprt &expr)
{
  assert(expr.id()==ID_notequal && expr.operands().size()==2);
  return static_cast<notequal_exprt &>(expr);
}

/*! \brief array index operator
*/
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

/*! \brief Cast a generic exprt to an \ref index_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * index_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref index_exprt
 *
 * \ingroup gr_std_expr
*/
const index_exprt &to_index_expr(const exprt &expr);
/*! \copydoc to_index_expr(const exprt &)
 * \ingroup gr_std_expr
*/
index_exprt &to_index_expr(exprt &expr);

/*! \brief array constructor from single element
*/
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

/*! \brief Cast a generic exprt to an \ref array_of_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * array_of_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref array_of_exprt
 *
 * \ingroup gr_std_expr
*/
const array_of_exprt &to_array_of_expr(const exprt &expr);
/*! \copydoc to_array_of_expr(const exprt &)
 * \ingroup gr_std_expr
*/
array_of_exprt &to_array_of_expr(exprt &expr);

/*! \brief array constructor from list of elements
*/
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

/*! \brief Cast a generic exprt to an \ref array_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * array_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref array_exprt
 *
 * \ingroup gr_std_expr
*/
const array_exprt &to_array_expr(const exprt &expr);
/*! \copydoc to_array_expr(const exprt &)
 * \ingroup gr_std_expr
*/
array_exprt &to_array_expr(exprt &expr);

/*! \brief array constructor from list of elements
*/
class vector_exprt:public exprt
{
public:
  inline vector_exprt():exprt(ID_vector)
  {
  }
 
  explicit inline vector_exprt(const typet &_type):
    exprt(ID_vector, _type)
  {
  }
 
  friend inline const vector_exprt &to_vector_expr(const exprt &expr)
  {
    assert(expr.id()==ID_vector);
    return static_cast<const vector_exprt &>(expr);
  }

  friend inline vector_exprt &to_vector_expr(exprt &expr)
  {
    assert(expr.id()==ID_vector);
    return static_cast<vector_exprt &>(expr);
  }
};

/*! \brief Cast a generic exprt to an \ref vector_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * vector_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref vector_exprt
 *
 * \ingroup gr_std_expr
*/
const vector_exprt &to_vector_expr(const exprt &expr);
/*! \copydoc to_vector_expr(const exprt &)
 * \ingroup gr_std_expr
*/
vector_exprt &to_vector_expr(exprt &expr);

/*! \brief union constructor from single element
*/
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

/*! \brief Cast a generic exprt to a \ref union_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * union_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref union_exprt
 *
 * \ingroup gr_std_expr
*/
const union_exprt &to_union_expr(const exprt &expr);
/*! \copydoc to_union_expr(const exprt &)
 * \ingroup gr_std_expr
*/
union_exprt &to_union_expr(exprt &expr);

/*! \brief struct constructor from list of elements
*/
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

/*! \brief Cast a generic exprt to a \ref struct_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * struct_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref struct_exprt
 *
 * \ingroup gr_std_expr
*/
const struct_exprt &to_struct_expr(const exprt &expr);
/*! \copydoc to_struct_expr(const exprt &)
 * \ingroup gr_std_expr
*/
struct_exprt &to_struct_expr(exprt &expr);

/*! \brief TO_BE_DOCUMENTED
*/
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

/*! \brief Cast a generic exprt to an \ref object_descriptor_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * object_descriptor_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref object_descriptor_exprt
 *
 * \ingroup gr_std_expr
*/
const object_descriptor_exprt &to_object_descriptor_expr(const exprt &expr);
/*! \copydoc to_object_descriptor_expr(const exprt &)
 * \ingroup gr_std_expr
*/
object_descriptor_exprt &to_object_descriptor_expr(exprt &expr);

/*! \brief TO_BE_DOCUMENTED
*/
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

/*! \brief Cast a generic exprt to a \ref dynamic_object_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * dynamic_object_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref dynamic_object_exprt
 *
 * \ingroup gr_std_expr
*/
const dynamic_object_exprt &to_dynamic_object_expr(const exprt &expr);
/*! \copydoc to_dynamic_object_expr(const exprt &)
 * \ingroup gr_std_expr
*/
dynamic_object_exprt &to_dynamic_object_expr(exprt &expr);

/*! \brief semantic type conversion
*/
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

/*! \brief Cast a generic exprt to a \ref typecast_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * typecast_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref typecast_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const typecast_exprt &to_typecast_expr(const exprt &expr)
{
  assert(expr.id()==ID_typecast && expr.operands().size()==1);
  return static_cast<const typecast_exprt &>(expr);
}

/*! \copydoc to_typecast_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline typecast_exprt &to_typecast_expr(exprt &expr)
{
  assert(expr.id()==ID_typecast && expr.operands().size()==1);
  return static_cast<typecast_exprt &>(expr);
}

/*! \brief boolean AND
*/
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

/*! \brief Cast a generic exprt to a \ref typecast_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * and_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref and_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const and_exprt &to_and_expr(const exprt &expr)
{
  assert(expr.id()==ID_and);
  return static_cast<const and_exprt &>(expr);
}

/*! \copydoc to_and_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline and_exprt &to_and_expr(exprt &expr)
{
  assert(expr.id()==ID_and);
  return static_cast<and_exprt &>(expr);
}

/*! \brief boolean implication
*/
class implies_exprt:public binary_exprt
{
public:
  inline implies_exprt():binary_exprt(ID_implies, bool_typet())
  {
  }

  inline implies_exprt(const exprt &op0, const exprt &op1):
    binary_exprt(op0, ID_implies, op1, bool_typet())
  {
  }
};

/*! \brief Cast a generic exprt to a \ref implies_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * implies_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref implies_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const implies_exprt &to_implies_expr(const exprt &expr)
{
  assert(expr.id()==ID_implies && expr.operands().size()==2);
  return static_cast<const implies_exprt &>(expr);
}

/*! \copydoc to_implies_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline implies_exprt &to_implies_expr(exprt &expr)
{
  assert(expr.id()==ID_implies && expr.operands().size()==2);
  return static_cast<implies_exprt &>(expr);
}

/*! \brief boolean OR
*/
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

/*! \brief Cast a generic exprt to a \ref or_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * or_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref or_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const or_exprt &to_or_expr(const exprt &expr)
{
  assert(expr.id()==ID_or);
  return static_cast<const or_exprt &>(expr);
}

/*! \copydoc to_or_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline or_exprt &to_or_expr(exprt &expr)
{
  assert(expr.id()==ID_or);
  return static_cast<or_exprt &>(expr);
}

/*! \brief Bit-wise negation of bit-vectors
*/
class bitnot_exprt:public unary_exprt
{
public:
  inline bitnot_exprt():unary_exprt(ID_bitnot)
  {
  }

  explicit inline bitnot_exprt(const exprt &op):
    unary_exprt(ID_bitnot, op)
  {
  }
};

/*! \brief Bit-wise OR
*/
class bitor_exprt:public exprt
{
public:
  inline bitor_exprt():exprt(ID_bitor)
  {
  }

  inline bitor_exprt(const exprt &_op0, const exprt &_op1):
    exprt(ID_bitor, _op0.type())
  {
    copy_to_operands(_op0, _op1);
  }
};

/*! \brief Cast a generic exprt to a \ref bitor_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * bitor_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref bitor_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const bitor_exprt &to_bitor_expr(const exprt &expr)
{
  assert(expr.id()==ID_bitor);
  return static_cast<const bitor_exprt &>(expr);
}

/*! \copydoc to_bitor_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline bitor_exprt &to_bitor_expr(exprt &expr)
{
  assert(expr.id()==ID_bitor);
  return static_cast<bitor_exprt &>(expr);
}

/*! \brief Bit-wise XOR
*/
class bitxor_exprt:public exprt
{
public:
  inline bitxor_exprt():exprt(ID_bitxor)
  {
  }

  inline bitxor_exprt(const exprt &_op0, const exprt &_op1):
    exprt(ID_bitxor, _op0.type())
  {
    copy_to_operands(_op0, _op1);
  }
};

/*! \brief Cast a generic exprt to a \ref bitxor_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * bitxor_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref bitxor_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const bitxor_exprt &to_bitxor_expr(const exprt &expr)
{
  assert(expr.id()==ID_bitxor);
  return static_cast<const bitxor_exprt &>(expr);
}

/*! \copydoc to_bitxor_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline bitxor_exprt &to_bitxor_expr(exprt &expr)
{
  assert(expr.id()==ID_bitxor);
  return static_cast<bitxor_exprt &>(expr);
}

/*! \brief Bit-wise AND
*/
class bitand_exprt:public exprt
{
public:
  inline bitand_exprt():exprt(ID_bitand)
  {
  }

  inline bitand_exprt(const exprt &_op0, const exprt &_op1):
    exprt(ID_bitand, _op0.type())
  {
    copy_to_operands(_op0, _op1);
  }
};

/*! \brief Cast a generic exprt to a \ref bitand_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * bitand_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref bitand_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const bitand_exprt &to_bitand_expr(const exprt &expr)
{
  assert(expr.id()==ID_bitand);
  return static_cast<const bitand_exprt &>(expr);
}

/*! \copydoc to_bitand_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline bitand_exprt &to_bitand_expr(exprt &expr)
{
  assert(expr.id()==ID_bitand);
  return static_cast<bitand_exprt &>(expr);
}

/*! \brief A base class for shift operators
*/
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

  inline exprt &op()
  {
    return op0();
  }

  inline const exprt &op() const
  {
    return op0();
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

/*! \brief Cast a generic exprt to a \ref shift_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * shift_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref shift_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const shift_exprt &to_shift_expr(const exprt &expr)
{
  assert(expr.operands().size()==2);
  return static_cast<const shift_exprt &>(expr);
}

/*! \copydoc to_shift_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline shift_exprt &to_shift_expr(exprt &expr)
{
  assert(expr.operands().size()==2);
  return static_cast<shift_exprt &>(expr);
}

/*! \brief Left shift
*/
class shl_exprt:public shift_exprt
{
public:
  inline shl_exprt():shift_exprt(ID_shl)
  {
  }

  inline shl_exprt(const exprt &_src, const exprt &_distance):shift_exprt(_src, ID_shl, _distance)
  {
  }
};

/*! \brief Arithmetic right shift
*/
class ashr_exprt:public shift_exprt
{
public:
  inline ashr_exprt():shift_exprt(ID_shl)
  {
  }

  inline ashr_exprt(const exprt &_src, const exprt &_distance):shift_exprt(_src, ID_ashr, _distance)
  {
  }
};

/*! \brief Logical right shift
*/
class lshr_exprt:public shift_exprt
{
public:
  inline lshr_exprt():shift_exprt(ID_shl)
  {
  }

  inline lshr_exprt(const exprt &_src, const exprt &_distance):shift_exprt(_src, ID_lshr, _distance)
  {
  }
};

/*! \brief Extracts a single bit of a bit-vector operand
*/
class extractbit_exprt:public predicate_exprt
{
public:
  inline extractbit_exprt():predicate_exprt(ID_extractbit)
  {
    operands().resize(2);
  }

  inline extractbit_exprt(
    const exprt &_src,
    const exprt &_index):predicate_exprt(ID_extractbit, _src, _index)
  {
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

/*! \brief Cast a generic exprt to an \ref extractbit_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * extractbit_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref extractbit_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const extractbit_exprt &to_extractbit_expr(const exprt &expr)
{
  assert(expr.id()==ID_extractbit && expr.operands().size()==2);
  return static_cast<const extractbit_exprt &>(expr);
}

/*! \copydoc to_extractbit_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline extractbit_exprt &to_extractbit_expr(exprt &expr)
{
  assert(expr.id()==ID_extractbit && expr.operands().size()==2);
  return static_cast<extractbit_exprt &>(expr);
}

/*! \brief Extracts a sub-range of a bit-vector operand
*/
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

/*! \brief Cast a generic exprt to an \ref extractbits_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * extractbits_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref extractbits_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const extractbits_exprt &to_extractbits_expr(const exprt &expr)
{
  assert(expr.id()==ID_extractbits && expr.operands().size()==3);
  return static_cast<const extractbits_exprt &>(expr);
}

/*! \copydoc to_extractbits_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline extractbits_exprt &to_extractbits_expr(exprt &expr)
{
  assert(expr.id()==ID_extractbits && expr.operands().size()==3);
  return static_cast<extractbits_exprt &>(expr);
}

/*! \brief Operator to return the address of an object
*/
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

/*! \brief Cast a generic exprt to an \ref address_of_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * address_of_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref address_of_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const address_of_exprt &to_address_of_expr(const exprt &expr)
{
  assert(expr.id()==ID_address_of && expr.operands().size()==1);
  return static_cast<const address_of_exprt &>(expr);
}

/*! \copydoc to_address_of_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline address_of_exprt &to_address_of_expr(exprt &expr)
{
  assert(expr.id()==ID_address_of && expr.operands().size()==1);
  return static_cast<address_of_exprt &>(expr);
}

/*! \brief Boolean negation
*/
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

/*! \brief Operator to dereference a pointer
*/
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

/*! \brief Cast a generic exprt to a \ref dereference_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * dereference_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref dereference_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const dereference_exprt &to_dereference_expr(const exprt &expr)
{
  assert(expr.id()==ID_dereference && expr.operands().size()==1);
  return static_cast<const dereference_exprt &>(expr);
}

/*! \copydoc to_dereference_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline dereference_exprt &to_dereference_expr(exprt &expr)
{
  assert(expr.id()==ID_dereference && expr.operands().size()==1);
  return static_cast<dereference_exprt &>(expr);
}

/*! \brief The trinary if-then-else operator
*/
class if_exprt:public exprt
{
public:
  inline if_exprt(const exprt &cond, const exprt &t, const exprt &f):
    exprt(ID_if, t.type())
  {
    copy_to_operands(cond, t, f);
  }

  inline if_exprt(const exprt &cond, const exprt &t, const exprt &f, const typet &type):
    exprt(ID_if, type)
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

/*! \brief Cast a generic exprt to an \ref if_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * if_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref if_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const if_exprt &to_if_expr(const exprt &expr)
{
  assert(expr.id()==ID_if && expr.operands().size()==3);
  return static_cast<const if_exprt &>(expr);
}

/*! \copydoc to_if_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline if_exprt &to_if_expr(exprt &expr)
{
  assert(expr.id()==ID_if && expr.operands().size()==3);
  return static_cast<if_exprt &>(expr);
}

/*! \brief Operator to update elements in structs and arrays
    \remark This expression will eventually be replaced by separate
            array and struct update operators.
*/
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

/*! \brief Cast a generic exprt to a \ref with_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * with_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref with_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const with_exprt &to_with_expr(const exprt &expr)
{
  assert(expr.id()==ID_with && expr.operands().size()==3);
  return static_cast<const with_exprt &>(expr);
}

/*! \copydoc to_with_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline with_exprt &to_with_expr(exprt &expr)
{
  assert(expr.id()==ID_with && expr.operands().size()==3);
  return static_cast<with_exprt &>(expr);
}

/*! \brief update of one element of an array
*/
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

/*! \brief Cast a generic exprt to an \ref array_update_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * array_update_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref array_update_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const array_update_exprt &to_array_update_expr(const exprt &expr)
{
  assert(expr.id()==ID_array_update && expr.operands().size()==3);
  return static_cast<const array_update_exprt &>(expr);
}

/*! \copydoc to_array_update_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline array_update_exprt &to_array_update_expr(exprt &expr)
{
  assert(expr.id()==ID_array_update && expr.operands().size()==3);
  return static_cast<array_update_exprt &>(expr);
}

/*! \brief Extract member of struct
*/
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

/*! \brief Cast a generic exprt to a \ref member_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * member_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref member_exprt
 *
 * \ingroup gr_std_expr
*/
inline const member_exprt &to_member_expr(const exprt &expr)
{
  assert(expr.id()==ID_member);
  return static_cast<const member_exprt &>(expr);
}

/*! \copydoc to_member_expr(const exprt &)
 * \ingroup gr_std_expr
*/
inline member_exprt &to_member_expr(exprt &expr)
{
  assert(expr.id()==ID_member);
  return static_cast<member_exprt &>(expr);
}

/*! \brief Evaluates to true if the operand is NaN
*/
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

/*! \brief IEEE-floating-point equality
*/
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

/*! \brief An expression denoting a type
*/
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

/*! \brief A constant literal expression
*/
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

/*! \brief Cast a generic exprt to a \ref constant_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * constant_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref constant_exprt
 *
 * \ingroup gr_std_expr
*/
inline const constant_exprt &to_constant_expr(const exprt &expr)
{
  assert(expr.id()==ID_constant);
  return static_cast<const constant_exprt &>(expr);
}

/*! \copydoc to_constant_expr(const exprt &)
 * \ingroup gr_std_expr
*/
inline constant_exprt &to_constant_expr(exprt &expr)
{
  assert(expr.id()==ID_constant);
  return static_cast<constant_exprt &>(expr);
}

/*! \brief The boolean constant true
*/
class true_exprt:public constant_exprt
{
public:
  inline true_exprt():constant_exprt(bool_typet())
  {
    set_value(ID_true);
  }
};

/*! \brief The boolean constant false
*/
class false_exprt:public constant_exprt
{
public:
  inline false_exprt():constant_exprt(bool_typet())
  {
    set_value(ID_false);
  }
};

/*! \brief The NIL expression
*/
class nil_exprt:public exprt
{
public:
  inline nil_exprt():exprt(static_cast<const exprt &>(get_nil_irep()))
  {
  }
};

/*! \brief The null pointer constant
*/
class null_pointer_exprt:public constant_exprt
{
public:
  explicit null_pointer_exprt(const pointer_typet &type):constant_exprt(type)
  {
    set_value(ID_NULL);
  }
};

/*! \brief application of (mathematical) function
*/
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
};

/*! \brief Cast a generic exprt to a \ref function_application_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * function_application_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref function_application_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const function_application_exprt &to_function_application_expr(const exprt &expr)
{
  assert(expr.id()==ID_function_application && expr.operands().size()==2);
  return static_cast<const function_application_exprt &>(expr);
}

/*! \copydoc to_function_application_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline function_application_exprt &to_function_application_expr(exprt &expr)
{
  assert(expr.id()==ID_function_application && expr.operands().size()==2);
  return static_cast<function_application_exprt &>(expr);
}

/*! \brief Concatenation of bit-vector operands
 *
 * This expression takes any number of operands
 * (a restriction to make this binary will happen in the future).
 * The ordering of the operands is the same as in the _new_ SMT 1.x standard,
 * i.e., most-significant operands come first.
*/
class concatenation_exprt:public exprt
{
public:
  inline concatenation_exprt():exprt(ID_concatenation)
  {
  }

  explicit inline concatenation_exprt(const typet &_type):
    exprt(ID_concatenation, _type)
  {
  }
  
  explicit inline concatenation_exprt(
    const exprt &_op0, const exprt &_op1, const typet &_type):
    exprt(ID_concatenation, _type)
  {
    copy_to_operands(_op0, _op1);
  }  
};

/*! \brief Cast a generic exprt to a \ref concatenation_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * concatenation_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref concatenation_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const concatenation_exprt &to_concatenation_expr(const exprt &expr)
{
  assert(expr.id()==ID_concatenation);
  return static_cast<const concatenation_exprt &>(expr);
}

/*! \copydoc to_concatenation_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline concatenation_exprt &to_concatenation_expr(exprt &expr)
{
  assert(expr.id()==ID_concatenation);
  return static_cast<concatenation_exprt &>(expr);
}

/*! \brief Evaluates to true if the two pointer
           operands point to the same object
*/
class same_object_exprt:public binary_relation_exprt
{
public:
  inline same_object_exprt(const exprt &ptr1, const exprt &ptr2):
    binary_relation_exprt(ptr1, "same-object", ptr2)
  {
  }
};

/*! \brief Base class for all side effects
    \remark Will eventually be replaced by side_effect_exprt
*/
class sideeffect_exprt:public exprt
{
public:
  inline sideeffect_exprt(
    const irep_idt &_statement,
    const typet &type):exprt(ID_sideeffect, type)
  {
    set_statement(_statement);
  }
  
  inline irep_idt get_statement() const
  {
    return get(ID_statement);
  }

  inline void set_statement(const irep_idt &_statement)
  {
    set(ID_statement, _statement);
  }
};

extern inline const sideeffect_exprt &to_sideeffect_expr(const exprt &expr)
{
  assert(expr.id()==ID_sideeffect);
  return static_cast<const sideeffect_exprt &>(expr);
}

/*! \brief A side effect that returns a non-deterministically chosen value
    \remark Will be replaced by side_effect_nondet_exprt
*/
class nondet_exprt:public sideeffect_exprt
{
public:
  inline explicit nondet_exprt(const typet &_type):
    sideeffect_exprt(ID_nondet, _type)
  {
  }
};

/*! \brief An expression denoting infinity
*/
class infinity_exprt:public exprt
{
public:
  inline explicit infinity_exprt(const typet &_type):
    exprt(ID_infinity, _type)
  {
  }
};

#endif
