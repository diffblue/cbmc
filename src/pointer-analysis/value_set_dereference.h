/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DEREFERENCE_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DEREFERENCE_H

#include <set>
#include <string>

#include <util/hash_cont.h>
#include <util/std_expr.h>

#include "dereference_callback.h"

class symbol_tablet;
class guardt;
class optionst;
class modet;
class symbolt;

/*! \brief TO_BE_DOCUMENTED
*/
class value_set_dereferencet
{
public:
  /*! \brief Constructor 
   * \param _ns Namespace
   * \param _new_symbol_table A symbol_table to store new symbols in
   * \param _options Options, in particular whether pointer checks are
            to be performed
   * \param _dereference_callback Callback object for error reporting
  */
  value_set_dereferencet(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    const optionst &_options,
    dereference_callbackt &_dereference_callback):
    ns(_ns),
    new_symbol_table(_new_symbol_table),
    options(_options),
    dereference_callback(_dereference_callback)
  { }

  virtual ~value_set_dereferencet() { }
  
  typedef enum { READ, WRITE } modet;
  
  /*! 
   * The method 'dereference' dereferences the
   * given pointer-expression. Any errors are
   * reported to the callback method given in the
   * constructor.
   *
   * \param pointer A pointer-typed expression, to
            be dereferenced.
   * \param guard A guard, which is assumed to hold when
            dereferencing.
   * \param mode Indicates whether the dereferencing
            is a load or store.
  */

  virtual exprt dereference(
    const exprt &pointer,
    const guardt &guard,
    const modet mode);
    
  /*! \brief Returns 'true' iff the given expression contains unary '*'
  */
  static bool has_dereference(const exprt &expr);

  typedef hash_set_cont<exprt, irep_hash> expr_sett;

private:
  const namespacet &ns;
  symbol_tablet &new_symbol_table;
  const optionst &options;
  dereference_callbackt &dereference_callback;
  static unsigned invalid_counter;

  bool dereference_type_compare(
    const typet &object_type,
    const typet &dereference_type) const;

  void offset_sum(
    exprt &dest,
    const exprt &offset) const;
    
  class valuet
  {
  public:
    exprt value;
    exprt pointer_guard;
    
    valuet():value(nil_exprt()), pointer_guard(false_exprt())
    {
    }
  };
  
  valuet build_reference_to(
    const exprt &what, 
    const modet mode,
    const exprt &pointer,
    const guardt &guard);

  bool get_value_guard(
    const exprt &symbol,
    const exprt &premise,
    exprt &value);
             
  static const exprt &get_symbol(const exprt &object);
  
  void bounds_check(const index_exprt &expr, const guardt &guard);
  void valid_check(const exprt &expr, const guardt &guard, const modet mode);
  
  void invalid_pointer(const exprt &expr, const guardt &guard);

  bool memory_model(
    exprt &value,
    const typet &type,
    const guardt &guard,
    const exprt &offset);

  bool memory_model_conversion(
    exprt &value,
    const typet &type,
    const guardt &guard,
    const exprt &offset);
    
  bool memory_model_bytes(
    exprt &value,
    const typet &type,
    const guardt &guard,
    const exprt &offset);
};

#endif
