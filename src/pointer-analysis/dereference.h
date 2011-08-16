/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_DEREFERENCE_H
#define CPROVER_POINTER_ANALYSIS_DEREFERENCE_H

#include <set>

#include <expr.h>
#include <hash_cont.h>
#include <guard.h>
#include <namespace.h>
#include <options.h>
#include <std_expr.h>

#include "value_sets.h"

class dereference_callbackt
{
public:
  virtual ~dereference_callbackt()
  {
  }

  virtual void dereference_failure(
    const std::string &property,
    const std::string &msg,
    const guardt &guard)=0;

  typedef hash_set_cont<exprt, irep_hash> expr_sett;

  virtual void get_value_set(
    const exprt &expr,
    value_setst::valuest &value_set)=0;
  
  virtual bool has_failed_symbol(
    const exprt &expr,
    const symbolt *&symbol)=0;
};

class dereferencet
{
public:
  /*! \brief Constructor 
   * \param _ns Namespace
   * \param _new_context A context to store new symbols in
   * \param _options Options, in particular whether pointer checks are
            to be performed
   * \param _dereference_callback Callback object for error reporting
  */
  dereferencet(
    const namespacet &_ns,
    contextt &_new_context,
    const optionst &_options,
    dereference_callbackt &_dereference_callback):
    ns(_ns),
    new_context(_new_context),
    options(_options),
    dereference_callback(_dereference_callback)
  { }

  virtual ~dereferencet() { }
  
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
  contextt &new_context;
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
  
  void bounds_check(const class index_exprt &expr, const guardt &guard);
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

  static irep_idt byte_extract_id();
};

#endif
