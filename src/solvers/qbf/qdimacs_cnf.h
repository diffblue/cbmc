/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_QBF_QDIMACS_CNF_H
#define CPROVER_QBF_QDIMACS_CNF_H

#include <set>
#include <iostream>

#include "../sat/dimacs_cnf.h"

class qdimacs_cnft:public dimacs_cnft
{
public:
  qdimacs_cnft() { }
  virtual ~qdimacs_cnft() { }

  virtual void write_qdimacs_cnf(std::ostream &out);

  // dummy functions

  virtual const std::string solver_text()
  {
    return "QDIMACS CNF";
  }

  class quantifiert
  {
  public:
    typedef enum { NONE, EXISTENTIAL, UNIVERSAL } typet;
    typet type;
    unsigned var_no;

    quantifiert():type(NONE), var_no(0)
    {
    }

    quantifiert(typet _type, literalt _l):type(_type), var_no(_l.var_no())
    {
    }

    friend bool operator==(const quantifiert &a, const quantifiert &b)
    {
      return a.type==b.type && a.var_no==b.var_no;
    }

    size_t hash() const
    {
      return var_no^(type<<24);
    }
  };

  // quantifiers
  typedef std::vector<quantifiert> quantifierst;
  quantifierst quantifiers;

  virtual void add_quantifier(const quantifiert &quantifier)
  {
    quantifiers.push_back(quantifier);
  }

  void add_quantifier(const quantifiert::typet type, const literalt l)
  {
    add_quantifier(quantifiert(type, l));
  }

  bool is_quantified(const literalt l) const;
  bool find_quantifier(const literalt l, quantifiert &q) const;

  virtual void set_quantifier(const quantifiert::typet type, const literalt l);
  void copy_to(qdimacs_cnft &cnf) const;

  friend bool operator==(const qdimacs_cnft &a, const qdimacs_cnft &b);
  size_t hash() const;

protected:
  void write_prefix(std::ostream &out) const;
};

#endif
