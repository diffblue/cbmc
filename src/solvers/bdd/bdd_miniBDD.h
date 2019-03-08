/*******************************************************************\

Module: Binary Decision Diagrams

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Interface to miniBDD functions that are used in CBMC
/// BDD functions should only be accessed through this header file.
/// That way, in case we want to change the underlying implementation of BDDs,
/// we will only have to substitute another header file for this one.

#ifndef CPROVER_SOLVERS_BDD_BDD_MINIBDD_H
#define CPROVER_SOLVERS_BDD_BDD_MINIBDD_H

#include <unordered_map>

#include <solvers/bdd/miniBDD/miniBDD.h>

class bdd_managert;
class bddt;
class bdd_nodet;

/// Low level access to the structure of the BDD, read-only.
class bdd_nodet
{
public:
  /// is_constant has to be true for `true` and `false` and to distinguish
  /// between the two, is_complement has to be true for the constant `false`.
  bool is_constant() const
  {
    return node->node_number <= 1;
  }

  bool is_complement() const
  {
    return node->node_number == 0;
  }

  /// Type of indexes of Boolean variables
  using indext = std::size_t;

  /// Label on the node, corresponds to the index of a Boolean variable
  indext index() const
  {
    return bdd_var_to_index.at(node->var);
  }

  bdd_nodet then_branch() const
  {
    return bdd_nodet(node->high.node, bdd_var_to_index);
  }

  bdd_nodet else_branch() const
  {
    return bdd_nodet(node->low.node, bdd_var_to_index);
  }

  /// Return type for \ref id()
  using idt = mini_bdd_nodet *;

  /// Unique identifier of the node
  idt id() const
  {
    return node;
  }

private:
  mini_bdd_nodet *node;

  // Should be owned by the BDD manager
  const std::unordered_map<std::size_t, std::size_t> &bdd_var_to_index;

  explicit bdd_nodet(
    mini_bdd_nodet *node,
    const std::unordered_map<std::size_t, std::size_t> &bdd_var_to_index)
    : node(node), bdd_var_to_index(bdd_var_to_index)
  {
  }

  friend class bdd_managert;
};

/// Logical operations on BDDs
class bddt : private mini_bddt
{
public:
  bool equals(const bddt &other) const
  {
    return node == other.node;
  }

  bool is_true() const
  {
    return mini_bddt::is_true();
  }

  bool is_false() const
  {
    return mini_bddt::is_false();
  }

  bddt bdd_not() const
  {
    return bddt(!(*this));
  }

  bddt bdd_or(const bddt &other) const
  {
    return bddt(*this | other);
  }

  bddt bdd_and(const bddt &other) const
  {
    return bddt(*this & other);
  }

  bddt bdd_xor(const bddt &other) const
  {
    return bddt(*this ^ other);
  }

  static bddt bdd_ite(const bddt &i, const bddt &t, const bddt &e)
  {
    return i.bdd_and(t).bdd_or(i.bdd_not().bdd_and(e));
  }

  bddt constrain(const bddt &other)
  {
    // This is correct, though not very useful
    return bddt(*this);
  }

  bddt &operator=(const bddt &other)
  {
    if(this != &other)
      mini_bddt::operator=(other);
    return *this;
  }

private:
  friend class bdd_managert;
  explicit bddt(const mini_bddt &bdd) : mini_bddt(bdd)
  {
  }
};

/// Manager for BDD creation
class bdd_managert : private mini_bdd_mgrt
{
public:
  bddt bdd_true()
  {
    return bddt(True());
  }

  bddt bdd_false()
  {
    return bddt(False());
  }

  bddt bdd_variable(bdd_nodet::indext index)
  {
    auto it = index_to_bdd.find(index);
    if(it != index_to_bdd.end())
      return it->second;
    auto var = Var(std::to_string(index));
    auto emplace_result = index_to_bdd.emplace(index, bddt(var));
    bdd_var_to_index[var.var()] = index;
    return emplace_result.first->second;
  }

  bdd_nodet bdd_node(const bddt &bdd) const
  {
    return bdd_nodet(bdd.node, bdd_var_to_index);
  }

  bdd_managert(const bdd_managert &) = delete;
  bdd_managert() = default;

private:
  std::unordered_map<std::size_t, bddt> index_to_bdd;
  std::unordered_map<std::size_t, std::size_t> bdd_var_to_index;
};

#endif // CPROVER_SOLVERS_BDD_BDD_MINIBDD_H
