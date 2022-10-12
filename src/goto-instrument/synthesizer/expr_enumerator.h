/*******************************************************************\
Module: Enumerator Interface
Author: Qinheping Hu
\*******************************************************************/

/// \file
/// Enumerator Interface

#ifndef CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_EXPR_ENUMERATOR_H
#define CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_EXPR_ENUMERATOR_H

#include <util/std_expr.h>

#include "synthesizer_utils.h"

#include <map>

typedef std::list<exprt> expr_listt;
typedef std::set<exprt> expr_sett;
typedef std::list<std::size_t> partitiont;

/*
  This is the interface of grammar-based enumerators. Users can specify tree
  grammars, and enumerate expressions derived by the grammars using these
  enumerators. A tree grammar consists of a finite set of nonterminals and
  a finite set of productions of the form A -> t where A is some nonterminal,
  and t is some tree composed from nonterminal symbols and constants.

  In the level of productions, we introduce three classes of enumerators:
  1. `leaf_enumeratort` enumerates `exprt`-typed expressions. It is used
     to enumerate leaves of trees derived from the tree grammar.
     Example:
     a `leaf_enumeratort` with `leaf_exprs` {0} enumerates expressions derived
     from the production
     * -> 0.
  2. `non_leaf_enumeratort` enumerates expressions recursively built from
     sub-trees---trees enumerated by sub-enumerators.
     Example:
     a `non_leaf_enumeratort` with `sub_enumerators` {A, B} and `op` +
     enumerates expressions derived from the production
     * -> A + B.
  3. `alternatives_enumeratort` enumerates expressions that can be enumerated
     by any of its `sub_enumerators`
     Example:
     a `alternatives_enumeratort` with `sub_enumerators` the enumerators in
     the Example 1 and 2 enumerates expressions derived from the production
     * -> 0 | A + B.

  One missing part in the above enumerators is the left-hand-side of
  productions, it should be a nonterminal symbol associated with a finite set
  of productions. So we introduce `recursive_enumerator_placeholdert` for
  nonterminal symbols, and `recursive_enumerator_factoryt` for grammars.
  Each placeholder has an identifier, and corresponds to a nonterminal in the
  grammar. Each factory maintains a map from identifier to placeholder, and a
  map from identifiers to placeholder's productions.

  As an example, to specify a grammar G with two nonterminals A and B, and two
  productions
  A -> A + B | 0
  B -> 1.
  We need to construct a factory with two placeholders ph_A and ph_b whose
  identifiers are "A" and "B", respectively.
  The factory should contain a set {ph_A, ph_B}, and a map
  {("A", E_A), ("B", E_B)}
  where the alternatives enumerator E_A is for the production
  -> A + B | 0
  and the alternatives enumerator E_B is for the production
  -> 1 | 2.
  Note that E_A contains a binary non-leaf enumerator E_plus with
  sub-enumerators (ph_A, ph_B) and operator `ID_plus`, and a leaf enumerator
  E_0 with `leaf_exprs` {0}. E_B contains a leaf enumerator E_1 with
  `leaf_exprs` {1} and a leaf enumerator E_2 with `leaf_exprs` {2}.

  Let [E, n] to be the result of enumeration E.enumerate(n)---expressions with
  size n enumerated by the enumerator E. To enumerate expressions with size 5
  in L(A) in the above example, the algorithm works as follow.
  [ph_A, 5] = [E_A, 5]    looking up "A" from `productions_map` of ph_A.factory
            = [E_plus, 5] \/ [E_0, 5]
            = [E_plus, 5] \/ {} = [E_plus, 5]
  [E_0, 5] = {} as leaf enumerator enumerates only expressions with size 1.

  To enumerate [E_plus, 5], we first enumerate expressions from two
  sub-enumerators E_A and E_B of E_plus, and then combine them using the
  operator ID_plus. In E_plus, the size of the operator ID_plus is 1, so the
  sum of sizes of two sub-expressions should be 4. There are three way to
  partition 4: (3, 1), (2, 2), and (1, 3). So
  [E_plus, 5] = [E_A, 3]*[E_B, 1] \/ [E_A, 2]*[E_B, 2] \/ [E_A, 1]*[E_B, 3]
  Note that E_B contain only leaf expressions. Therefore [E_B, 1] = {1, 2}, and
  [E_B, n] = {} for all n > 1. The * operator is the Cartesian products
  instantiated with plus operator.
  [E_plus, 5] = [E_A, 3]*[E_B, 1] \/ [E_A, 2]*[E_B, 2] \/ [E_A, 1]*[E_B, 3]
              = [E_A, 3]*{1, 2} \/ [E_A, 2]*{} \/ [E_A, 2]*{}
              = [E_A, 3]*{1, 2} \/ {} \/ {}
              = [E_A, 3]*{1, 2}
              = ([E_A, 1]*[E_B, 1])*{1, 2}
              = ({0}*{1,2})*{1, 2}
              = {0+1, 0+2}*{1, 2}
              = {(0+1)+1, (0+2)+1, (0+1)+2, (0+2)+2}
  So, expressions in L(A) are {(0+1)+1, (0+2)+1, (0+1)+2, (0+2)+2}.

  Why Cartesian products.
  For a grammar,
  A -> B + B
  B -> 1 | 2,
  the expressions enumerated by B are {1, 2}. To enumerate expressions in L(A).
  We need to combine sub-expressions {1, 2} into a plus-expression.
  {1, 2} + {1, 2}
  Because each nonterminal B can yield either 1 and 2 independently, we have to
  combine sub-expressions as their cartesian products.
  {1 + 1, 1 + 2, 2 + 1, 2 + 2}.
*/

/// A base class for expression enumerators.
class enumerator_baset
{
public:
  explicit enumerator_baset(const namespacet &ns) : ns(ns)
  {
  }

  virtual expr_sett enumerate(const std::size_t size) const = 0;

  enumerator_baset(const enumerator_baset &other) = delete;
  enumerator_baset &operator=(const enumerator_baset &other) = delete;

  virtual ~enumerator_baset() = default;

protected:
  const namespacet &ns;
};

typedef std::list<const enumerator_baset *> enumeratorst;

/// Enumerator that enumerates leaf expressions from a given list.
/// Leaf expressions are complete expressions with no placeholder.
class leaf_enumeratort : public enumerator_baset
{
public:
  leaf_enumeratort(const expr_sett &leaf_exprs, const namespacet &ns)
    : enumerator_baset(ns), leaf_exprs(leaf_exprs)
  {
  }

  /// Enumerate expressions in the set of `leaf_exprs`.
  expr_sett enumerate(const std::size_t size) const override;

protected:
  const expr_sett leaf_exprs;
};

/// Non-leaf enumerator enumerates expressions of form
/// f(a_1, a_2, ..., a_n)
/// where a_i's are sub-expressions enumerated by sub-enumerators.
class non_leaf_enumeratort : public enumerator_baset
{
public:
  /// \param enumerators a list of enumerator (e_1,...,e_n),
  /// where a_i in the expressions enumerated by this enumerator can be
  /// enumerated by the enumerator e_i.
  /// \param partition_check an optional function checking whether a partition
  /// can be safely discarded.
  /// \param ns namesapce used by `simplify_expr`.
  non_leaf_enumeratort(
    const enumeratorst &enumerators,
    const std::function<bool(const partitiont &)> partition_check,
    const namespacet &ns)
    : enumerator_baset(ns),
      arity(enumerators.size()),
      sub_enumerators(enumerators),
      is_good_partition(partition_check)
  {
    INVARIANT(
      arity > 1, "arity should be greater than one for non_leaf_enumeratort");
  }

  /// As default: no optimization. `partition_check` Accept all partitions.
  non_leaf_enumeratort(const enumeratorst &enumerators, const namespacet &ns)
    : non_leaf_enumeratort(
        enumerators,
        [](const partitiont &) { return true; },
        ns)
  {
  }

  expr_sett enumerate(const std::size_t size) const override;

  /// Given a list `enumerators` of enumerators, return the Cartesian product
  /// of expressions enumerated by each enumerator in the list.
  std::set<expr_listt> cartesian_product_of_enumerators(
    const enumeratorst &enumerators,
    const enumeratorst::const_iterator &it,
    const partitiont &partition,
    const partitiont::const_iterator &it_partition) const;

  /// Enumerate all partitions of n into k components.
  /// Order of partitions is considered relevant.
  std::list<partitiont>
  get_partitions(const std::size_t n, const std::size_t k) const;

  /// As default, keep all expression tuples.
  virtual bool is_equivalence_class_representation(const expr_listt &es) const
  {
    return true;
  }

protected:
  /// Combine a list of sub-expressions to construct the top-level expression.
  virtual exprt instantiate(const expr_listt &exprs) const = 0;

  const std::size_t arity;
  const enumeratorst sub_enumerators;
  const std::function<bool(const partitiont &)> is_good_partition;
};

/// Enumerator that enumerates binary functional expressions.
class binary_functional_enumeratort : public non_leaf_enumeratort
{
public:
  binary_functional_enumeratort(
    const irep_idt &op,
    const enumerator_baset &enumerator_1,
    const enumerator_baset &enumerator_2,
    const std::function<bool(const partitiont &)> partition_check,
    const bool exchangeable,
    const namespacet &ns)
    : non_leaf_enumeratort({&enumerator_1, &enumerator_2}, partition_check, ns),
      is_exchangeable(exchangeable),
      op_id(op)
  {
  }

  binary_functional_enumeratort(
    const irep_idt &op,
    const enumerator_baset &enumerator_1,
    const enumerator_baset &enumerator_2,
    const std::function<bool(const partitiont &)> partition_check,
    const namespacet &ns)
    : binary_functional_enumeratort(
        op,
        enumerator_1,
        enumerator_2,
        partition_check,
        &enumerator_1 == &enumerator_2,
        ns)
  {
  }

  binary_functional_enumeratort(
    const irep_idt &op,
    const enumerator_baset &enumerator_1,
    const enumerator_baset &enumerator_2,
    const namespacet &ns)
    : binary_functional_enumeratort(
        op,
        enumerator_1,
        enumerator_2,
        [](const partitiont &) { return true; },
        ns)
  {
  }

  bool is_commutative(const irep_idt &op) const;

  /// Determine whether a tuple of expressions is the representation of some
  /// equivalence class.
  bool
  is_equivalence_class_representation(const expr_listt &exprs) const override;

protected:
  exprt instantiate(const expr_listt &exprs) const override;

  // Whether the two sub-enumerators are exchangeable---they enumerate the same
  // set of expressions.
  const bool is_exchangeable = false;

  const irep_idt &op_id;
};

/// Enumerators that enumerates expressions in the union of enumerated
/// expressions of sub-enumerators.
/// For sub enumerator E_1 | E_2 | ... | E_n, an alternatives enumerator
/// enumerates e in one of `E_i.enumerate(size)`.
class alternatives_enumeratort : public enumerator_baset
{
public:
  alternatives_enumeratort(
    const enumeratorst &enumerators,
    const namespacet &ns)
    : enumerator_baset(ns), sub_enumerators(enumerators)
  {
  }

  expr_sett enumerate(const std::size_t size) const override;

protected:
  const enumeratorst sub_enumerators;
};

class recursive_enumerator_placeholdert;

/// Factory for enumerator that can be used to represent a tree grammar.
class enumerator_factoryt
{
public:
  explicit enumerator_factoryt(const namespacet &ns) : ns(ns)
  {
  }

  /// Add a new placeholder/nonterminal to the grammar.
  void add_placeholder(const recursive_enumerator_placeholdert &placeholder);

  /// Attach `enumerators` to the placeholder with `id`.
  void
  attach_productions(const std::string &id, const enumeratorst &enumerators);

  /// Map from names of nonterminals to rhs of productions with lhs being them.
  /// Example: consider a nonterminal S -> 1 | 1 + S. This map will map the id
  /// "S" to a list of enumerators [E_1, E_2] where E_1 enumerates 1 and
  /// E_2 enumerates 1 + S.
  std::map<std::string, const enumeratorst> productions_map;

protected:
  const namespacet &ns;

  /// Set of nonterminals in the grammar.
  std::set<std::string> nonterminal_set;
};

/// Placeholders for actual enumerators, which represent nonterminals.
/// Example: consider the grammar
/// S -> N + N,
/// N -> N + 1 | 1.
/// The symbol N represents an enumerator in the lhs of the second production,
/// while it represents a placeholder in the rhs of both productions.
class recursive_enumerator_placeholdert : public enumerator_baset
{
public:
  /// \param factory the enumerator factory---a grammar---this enumerator
  /// belongs to.
  /// \param id the identifier of this placeholder.
  /// \param ns namesapce used for `simplify_expr`.
  recursive_enumerator_placeholdert(
    enumerator_factoryt &factory,
    const std::string &id,
    const namespacet &ns)
    : enumerator_baset(ns), identifier(id), factory(factory)
  {
    factory.add_placeholder(*this);
  }

  expr_sett enumerate(const std::size_t size) const override;

  const std::string identifier;

protected:
  const enumerator_factoryt &factory;
};

#endif // CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_EXPR_ENUMERATOR_H
