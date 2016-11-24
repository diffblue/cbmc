/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_CVC_CONV_H
#define CPROVER_PROP_CVC_CONV_H

#include <util/hash_cont.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/pointer_logic.h>

class cvc_convt:public prop_convt
{
public:
  cvc_convt(const namespacet &_ns,
            std::ostream &_out):
    prop_convt(_ns),
    out(_out),
    pointer_logic(_ns),
    no_boolean_variables(0)
  {
  }

  virtual ~cvc_convt() { }

  // API methods
  virtual void set_to(const exprt &expr, bool value);
  virtual literalt convert(const exprt &expr);
  virtual tvt l_get(literalt) const;
  virtual void print_assignment(std::ostream &out) const;

protected:
  std::ostream &out;

  virtual void convert_expr(const exprt &expr);
  virtual void convert_type(const typet &type);
  virtual void convert_address_of_rec(const exprt &expr);

  pointer_logict pointer_logic;  
  unsigned no_boolean_variables;
  
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
  
  std::vector<bool> boolean_assignment;

private:
  void convert_identifier(const std::string &identifier);
  void convert_literal(const literalt l);
  void find_symbols(const exprt &expr);
  void find_symbols(const typet &type);
  void convert_array_value(const exprt &expr);
  void convert_as_bv(const exprt &expr);
  void convert_array_index(const exprt &expr);
  static typet gen_array_index_type();
  static std::string bin_zero(unsigned bits);
  static std::string array_index_type();
  static std::string array_index(unsigned i);
  static std::string cvc_pointer_type();  
};

#endif
