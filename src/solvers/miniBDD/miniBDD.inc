#include <cassert>

// inline functions

mini_bddt::mini_bddt():node(0)
{
}

mini_bddt::mini_bddt(const mini_bddt &x):node(x.node)
{
  if(is_initialized()) node->add_reference();
}

mini_bddt::mini_bddt(class mini_bdd_nodet *_node):node(_node)
{
  if(is_initialized()) node->add_reference();
}

mini_bddt &mini_bddt::operator=(const mini_bddt &x)
{
  assert(&x!=this);
  clear();

  node=x.node;

  if(is_initialized()) node->add_reference();

  return *this;
}

mini_bddt::~mini_bddt()
{
  clear();
}

bool mini_bddt::is_constant() const
{
  assert(is_initialized());
  return node->node_number<=1;
}

bool mini_bddt::is_true() const
{
  assert(is_initialized());
  return node->node_number==1;
}

bool mini_bddt::is_false() const
{
  assert(is_initialized());
  return node->node_number==0;
}

unsigned mini_bddt::var() const
{
  assert(is_initialized());
  return node->var;
}

unsigned mini_bddt::node_number() const
{
  assert(is_initialized());
  return node->node_number;
}

const mini_bddt &mini_bddt::low() const
{
  assert(is_initialized());
  assert(node->node_number>=2);
  return node->low;
}

const mini_bddt &mini_bddt::high() const
{
  assert(is_initialized());
  assert(node->node_number>=2);
  return node->high;
}

void mini_bddt::clear()
{
  if(is_initialized())
  {
    node->remove_reference();
    node=NULL;
  }
}

mini_bdd_nodet::mini_bdd_nodet(
  class mini_bdd_mgrt *_mgr,
  unsigned _var, unsigned _node_number,
  const mini_bddt &_low, const mini_bddt &_high):
  mgr(_mgr), var(_var), node_number(_node_number),
  reference_counter(0),
  low(_low), high(_high)
{
}

mini_bdd_mgrt::var_table_entryt::var_table_entryt(
  const std::string &_label):label(_label)
{
}

const mini_bddt &mini_bdd_mgrt::True() const
{
  return true_bdd;
}

const mini_bddt &mini_bdd_mgrt::False() const
{
  return false_bdd;
}

void mini_bdd_nodet::add_reference()
{
  reference_counter++;
}

mini_bdd_mgrt::reverse_keyt::reverse_keyt(
  unsigned _var, const mini_bddt &_low, const mini_bddt &_high):
  var(_var), low(_low.node->node_number), high(_high.node->node_number)
{
}

std::size_t mini_bdd_mgrt::number_of_nodes()
{
  return nodes.size()-free.size();
}
