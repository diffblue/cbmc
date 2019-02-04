/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_QBF_QDIMACS_CNF_H
#define CPROVER_SOLVERS_QBF_QDIMACS_CNF_H

#include <set>
#include <iosfwd>

#include <solvers/sat/dimacs_cnf.h>

class qdimacs_cnft:public dimacs_cnft
{
public:
  explicit qdimacs_cnft(message_handlert &message_handler)
    : dimacs_cnft(message_handler)
  {
  }
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
    enum class typet { NONE, EXISTENTIAL, UNIVERSAL };
    typet type;
    unsigned var_no;

    quantifiert():type(typet::NONE), var_no(0)
    {
    }

    quantifiert(typet _type, literalt _l):type(_type), var_no(_l.var_no())
    {
    }

    bool operator==(const quantifiert &other) const
    {
      return type==other.type && var_no==other.var_no;
    }

    size_t hash() const
    {
      return var_no^(static_cast<int>(type)<<24);
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

  void add_existential_quantifier(const literalt l)
  {
    add_quantifier(quantifiert(quantifiert::typet::EXISTENTIAL, l));
  }

  void add_universal_quantifier(const literalt l)
  {
    add_quantifier(quantifiert(quantifiert::typet::UNIVERSAL, l));
  }

  bool is_quantified(const literalt l) const;
  bool find_quantifier(const literalt l, quantifiert &q) const;

  virtual void set_quantifier(const quantifiert::typet type, const literalt l);
  void copy_to(qdimacs_cnft &cnf) const;

  bool operator==(const qdimacs_cnft &other) const;

  size_t hash() const;

protected:
  void write_prefix(std::ostream &out) const;
};

#endif // CPROVER_SOLVERS_QBF_QDIMACS_CNF_H
