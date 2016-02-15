// A minimalistic BDD library, following Bryant's original paper
// and Henrik Reif Andersen's lecture notes
//
// Written by Daniel Kroening on the 28th of September 2009

#ifndef miniBDD_H
#define miniBDD_H

#include <list>
#include <vector>
#include <map>
#include <string>
#include <stack>

namespace miniBDD
{

class BDD
{
public:
  inline BDD();
  inline BDD(const BDD &x);
  inline ~BDD();

  // Boolean operators on BDDs
  BDD operator !() const;
  BDD operator ^(const BDD &) const;
  BDD operator ==(const BDD &) const;
  BDD operator &(const BDD &) const;
  BDD operator |(const BDD &) const;
  
  // copy operator
  inline BDD &operator=(const BDD &);
  
  inline bool is_constant() const;
  inline bool is_true() const;
  inline bool is_false() const;

  inline unsigned var() const;
  inline const BDD &low() const;
  inline const BDD &high() const;
  inline unsigned node_number() const;
  inline void clear();

  // internal  
  explicit inline BDD(class node *_node);
  class node *node;
};

class node
{
public:
  class mgr *mgr;
  unsigned var, node_number, reference_counter;
  BDD low, high;
  
  inline node(
    class mgr *_mgr,
    unsigned _var, unsigned _node_number,
    const BDD &_low, const BDD &_high);

  inline void add_reference();
  void remove_reference();
};

class mgr
{
public:
  mgr();
  ~mgr();

  BDD Var(const std::string &label);

  void DumpDot(std::ostream &out, bool supress_zero=false) const;
  void DumpTikZ(std::ostream &out, bool supress_zero=false, bool node_numbers=true) const;
  void DumpTable(std::ostream &out) const;

  inline const BDD &True() const;
  inline const BDD &False() const;
  
  friend class BDD;
  friend class node;
  
  // create a node (consulting the reverse-map)
  BDD mk(unsigned var, const BDD &low, const BDD &high);
  
  inline std::size_t number_of_nodes();
  
  struct var_table_entryt
  {
    std::string label;
    inline var_table_entryt(const std::string &_label);
  };  

  typedef std::vector<var_table_entryt> var_tablet;
  var_tablet var_table;  
  
protected:
  typedef std::list<node> nodest;
  nodest nodes;
  BDD true_bdd, false_bdd;
  
  // this is our reverse-map for nodes
  struct reverse_keyt
  {
    unsigned var, low, high;
    inline reverse_keyt(
      unsigned _var, const BDD &_low, const BDD &_high);
  };
  
  friend bool operator < (const reverse_keyt &x, const reverse_keyt &y);
  
  typedef std::map<reverse_keyt, node *> reverse_mapt;
  reverse_mapt reverse_map;
  
  typedef std::stack<node *> freet;
  freet free;
};

BDD restrict(const BDD &u, unsigned var, const bool value);
BDD exists(const BDD &u, unsigned var);
BDD substitute(const BDD &where, unsigned var, const BDD &by_what);
std::string cubes(const BDD &u);
bool OneSat(const BDD &v, std::map<unsigned, bool> &assignment);

} // namespace miniBDD

// inline functions
#include "miniBDD.inc"

#endif
