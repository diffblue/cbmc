#include <util/invariant.h>

// inline functions

inline mini_bddt::mini_bddt():node(nullptr)
{
}

inline mini_bddt::mini_bddt(const mini_bddt &x):node(x.node)
{
  if(is_initialized()) node->add_reference();
}

inline mini_bddt::mini_bddt(class mini_bdd_nodet *_node):node(_node)
{
  if(is_initialized()) node->add_reference();
}

inline mini_bddt &mini_bddt::operator=(const mini_bddt &x)
{
  PRECONDITION_WITH_DIAGNOSTICS(&x != this, "cannot assign itself");
  clear();

  node=x.node;

  if(is_initialized()) node->add_reference();

  return *this;
}

inline mini_bddt::~mini_bddt()
{
  clear();
}

inline bool mini_bddt::is_constant() const
{
  PRECONDITION_WITH_DIAGNOSTICS(is_initialized(), "BDD has to be initialized");
  return node->node_number<=1;
}

inline bool mini_bddt::is_true() const
{
  PRECONDITION_WITH_DIAGNOSTICS(is_initialized(), "BDD has to be initialized");
  return node->node_number==1;
}

inline bool mini_bddt::is_false() const
{
  PRECONDITION_WITH_DIAGNOSTICS(is_initialized(), "BDD has to be initialized");
  return node->node_number==0;
}

inline unsigned mini_bddt::var() const
{
  PRECONDITION_WITH_DIAGNOSTICS(is_initialized(), "BDD has to be initialized");
  return node->var;
}

inline unsigned mini_bddt::node_number() const
{
  PRECONDITION_WITH_DIAGNOSTICS(is_initialized(), "BDD has to be initialized");
  return node->node_number;
}

inline const mini_bddt &mini_bddt::low() const
{
  PRECONDITION_WITH_DIAGNOSTICS(is_initialized(), "BDD has to be initialized");
  PRECONDITION_WITH_DIAGNOSTICS(node->node_number >= 2, "only non-terminal nodes have out-going edges");
  return node->low;
}

inline const mini_bddt &mini_bddt::high() const
{
  PRECONDITION_WITH_DIAGNOSTICS(is_initialized(), "BDD has to be initialized");
  PRECONDITION_WITH_DIAGNOSTICS(node->node_number >= 2, "only non-terminal nodes have out-going edges");
  return node->high;
}

inline void mini_bddt::clear()
{
  if(is_initialized())
  {
    node->remove_reference();
    node=nullptr;
  }
}

inline mini_bdd_nodet::mini_bdd_nodet(
  class mini_bdd_mgrt *_mgr,
  unsigned _var, unsigned _node_number,
  const mini_bddt &_low, const mini_bddt &_high):
  mgr(_mgr), var(_var), node_number(_node_number),
  reference_counter(0),
  low(_low), high(_high)
{
}

inline mini_bdd_mgrt::var_table_entryt::var_table_entryt(
  const std::string &_label):label(_label)
{
}

inline const mini_bddt &mini_bdd_mgrt::True() const
{
  return true_bdd;
}

inline const mini_bddt &mini_bdd_mgrt::False() const
{
  return false_bdd;
}

inline void mini_bdd_nodet::add_reference()
{
  reference_counter++;
}

inline mini_bdd_mgrt::reverse_keyt::reverse_keyt(
  unsigned _var, const mini_bddt &_low, const mini_bddt &_high):
  var(_var), low(_low.node->node_number), high(_high.node->node_number)
{
}

inline std::size_t mini_bdd_mgrt::number_of_nodes()
{
  return nodes.size()-free.size();
}
