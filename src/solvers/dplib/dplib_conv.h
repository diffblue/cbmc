/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_DPLIB_CONV_H
#define CPROVER_PROP_DPLIB_CONV_H

#include <util/hash_cont.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/pointer_logic.h>

#include "dplib_prop.h"

class dplib_convt:public prop_convt
{
public:
  dplib_convt(
    const namespacet &_ns,
    std::ostream &_out):
    prop_convt(_ns),
    out(_out),
    pointer_logic(_ns) { }

  virtual ~dplib_convt() { }

protected:
  std::ostream &out;

  virtual literalt convert_rest(const exprt &expr);
  virtual void convert_dplib_expr(const exprt &expr);
  virtual void convert_dplib_type(const typet &type);
  virtual void set_to(const exprt &expr, bool value);
  virtual void convert_address_of_rec(const exprt &expr);

  pointer_logict pointer_logic;
  
private:
  void convert_identifier(const std::string &identifier);
  void find_symbols(const exprt &expr);
  void find_symbols(const typet &type);
  void convert_array_value(const exprt &expr);
  void convert_as_bv(const exprt &expr);
  void convert_array_index(const exprt &expr);
  static typet gen_array_index_type();
  static std::string bin_zero(unsigned bits);
  static std::string array_index_type();
  static std::string array_index(unsigned i);
  static std::string dplib_pointer_type();
  
  struct identifiert
  {
    typet type;
    exprt value;
    
    identifiert()
    {
      type.make_nil();
      value.make_nil();
    }
  };
  
  typedef hash_map_cont<irep_idt, identifiert, irep_id_hash>
    identifier_mapt;

  identifier_mapt identifier_map;
};

#endif
