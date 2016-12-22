#include <cassert>

// inline functions

BDD::BDD():node(0)
{
}

BDD::BDD(const BDD &x):node(x.node)
{
  if(is_initialized()) node->add_reference();
}

BDD::BDD(class node *_node):node(_node)
{
  if(is_initialized()) node->add_reference();
}

BDD &BDD::operator=(const BDD &x)
{
  assert(&x!=this);
  clear();

  node=x.node;

  if(is_initialized()) node->add_reference();

  return *this;
}

BDD::~BDD()
{
  clear();
}

bool BDD::is_constant() const
{
  assert(is_initialized());
  return node->node_number<=1;
}

bool BDD::is_true() const
{
  assert(is_initialized());
  return node->node_number==1;
}

bool BDD::is_false() const
{
  assert(is_initialized());
  return node->node_number==0;
}

unsigned BDD::var() const
{
  assert(is_initialized());
  return node->var;
}

unsigned BDD::node_number() const
{
  assert(is_initialized());
  return node->node_number;
}

const BDD &BDD::low() const
{
  assert(is_initialized());
  assert(node->node_number>=2);
  return node->low;
}

const BDD &BDD::high() const
{
  assert(is_initialized());
  assert(node->node_number>=2);
  return node->high;
}

void BDD::clear()
{
  if(is_initialized())
  {
    node->remove_reference();
    node=NULL;
  }
}

node::node(
  class mgr *_mgr,
  unsigned _var, unsigned _node_number,
  const BDD &_low, const BDD &_high):
  mgr(_mgr), var(_var), node_number(_node_number),
  reference_counter(0),
  low(_low), high(_high)
{
}

mgr::var_table_entryt::var_table_entryt(
  const std::string &_label):label(_label)
{
}

const BDD &mgr::True() const
{
  return true_bdd;
}

const BDD &mgr::False() const
{
  return false_bdd;
}

void node::add_reference()
{
  reference_counter++;
}

mgr::reverse_keyt::reverse_keyt(
  unsigned _var, const BDD &_low, const BDD &_high):
  var(_var), low(_low.node->node_number), high(_high.node->node_number)
{
}

std::size_t mgr::number_of_nodes()
{
  return nodes.size()-free.size();
}
