/*******************************************************************\

Module: Binary Decision Diagrams

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Interface to Cudd BDD functions that are used in CBMC
/// BDD functions should only be accessed through this header file.
/// That way, in case we want to change the underlying implementation of BDDs,
/// we will only have to substitute another header file for this one.

#ifndef CPROVER_SOLVERS_BDD_BDD_CUDD_H
#define CPROVER_SOLVERS_BDD_BDD_CUDD_H

#include <cplusplus/cuddObj.hh>

#include <util/narrow.h>

class bdd_managert;
class bddt;
class bdd_nodet;

/// Low level access to the structure of the BDD, read-only.
class bdd_nodet
{
public:
  bool is_constant() const
  {
    return Cudd_IsConstant(node) != 0;
  }

  bool is_complement() const
  {
    return Cudd_IsComplement(node) != 0;
  }

  /// Type of indexes of Boolean variables
  using indext = unsigned int;

  /// Label on the node, corresponds to the index of a Boolean variable
  indext index() const
  {
    return Cudd_NodeReadIndex(node);
  }

  bdd_nodet then_branch() const
  {
    return bdd_nodet(Cudd_T(node));
  }

  bdd_nodet else_branch() const
  {
    return bdd_nodet(Cudd_E(node));
  }

  /// Return type for \ref id()
  using idt = DdNode *;

  /// Unique identifier of the node
  idt id() const
  {
    return node;
  }

private:
  DdNode *node;
  explicit bdd_nodet(DdNode *node) : node(node)
  {
  }
  friend class bdd_managert;
};

/// Logical operations on BDDs
class bddt
{
public:
  bool equals(const bddt &other) const
  {
    return bdd == other.bdd;
  }

  bool is_true() const
  {
    return bdd.IsOne();
  }

  bool is_false() const
  {
    return bdd.IsZero();
  }

  bddt bdd_not() const
  {
    return bddt(!bdd);
  }

  bddt bdd_or(const bddt &other) const
  {
    return bddt(bdd.Or(other.bdd));
  }

  bddt bdd_and(const bddt &other) const
  {
    return bddt(bdd.And(other.bdd));
  }

  bddt bdd_xor(const bddt &other) const
  {
    return bddt(bdd.Xor(other.bdd));
  }

  static bddt bdd_ite(const bddt &i, const bddt &t, const bddt &e)
  {
    return bddt(i.bdd.Ite(t.bdd, e.bdd));
  }

  bddt constrain(const bddt &other)
  {
    return bddt(bdd.Constrain(other.bdd));
  }

  bddt &operator=(const bddt &other) = default;

private:
  BDD bdd;
  friend class bdd_managert;
  explicit bddt(BDD bdd) : bdd(std::move(bdd))
  {
  }
};

/// Manager for BDD creation
class bdd_managert
{
public:
  bdd_managert() : cudd()
  {
  }

  bdd_managert(const bdd_managert &) = delete;

  bddt bdd_true()
  {
    return bddt(cudd.bddOne());
  }

  bddt bdd_false()
  {
    return bddt(cudd.bddZero());
  }

  bddt bdd_variable(bdd_nodet::indext index)
  {
    return bddt(cudd.bddVar(narrow_cast<int>(index)));
  }

  bdd_nodet bdd_node(const bddt &bdd) const
  {
    return bdd_nodet(bdd.bdd.getNode());
  }

private:
  Cudd cudd;
};

#endif // CPROVER_SOLVERS_BDD_BDD_H
