/*******************************************************************\
Module: Enumerator Interface
Author: Qinheping Hu
\*******************************************************************/

#include "expr_enumerator.h"

#include <util/format_expr.h>
#include <util/simplify_expr.h>

expr_sett leaf_enumeratort::enumerate(const std::size_t size) const
{
  // Size of leaf expressions must be 1.
  if(size != 1)
    return {};

  return leaf_exprs;
}

expr_sett non_leaf_enumeratort::enumerate(const std::size_t size) const
{
  expr_sett result;

  // Enumerate nothing when `size` is too small to be partitioned.
  if(size - 1 < arity)
    return result;

  // For every possible partition, set `size` of
  // each sub-enumerator to be the corresponding component in the partition.
  for(const auto &partition : get_partitions(size - 1, arity))
  {
    if(!is_good_partition(partition))
      continue;

    // Compute the Cartesian product as result.
    for(const auto &product_tuple : cartesian_product_of_enumerators(
          sub_enumerators,
          sub_enumerators.begin(),
          partition,
          partition.begin()))
    {
      // Optimization: rule out equivalent expressions
      // using certain equivalence class.
      // Keep only representation tuple of each equivalence class.
      if(is_equivalence_class_representation(product_tuple))
        result.insert(simplify_expr(instantiate(product_tuple), ns));
    }
  }

  return result;
}

std::set<expr_listt> non_leaf_enumeratort::cartesian_product_of_enumerators(
  const enumeratorst &enumerators,
  const enumeratorst::const_iterator &it_enumerators,
  const partitiont &partition,
  const partitiont::const_iterator &it_partition) const
{
  INVARIANT(
    std::distance(it_enumerators, enumerators.end()) ==
      std::distance(it_partition, partition.end()),
    "Partition should have the same size as enumerators.");

  std::set<expr_listt> result;

  if(std::next(it_enumerators) == enumerators.end())
  {
    /// Current enumerator is the last enumerator.
    /// Add all expressions enumerated by `it_enumerators` to `result`.
    for(const auto &e : enumerators.back()->enumerate(*it_partition))
    {
      result.insert({e});
    }
  }
  else
  {
    /// First compute the Cartesian product of enumerators after
    /// `it_enumerators`. And then append the expressions enumerated by the
    /// `it_enumerators` to every list in the Cartesian product.
    for(const auto &sub_tuple : cartesian_product_of_enumerators(
          enumerators,
          std::next(it_enumerators),
          partition,
          std::next(it_partition)))
    {
      for(const auto &elem : (*it_enumerators)->enumerate(*it_partition))
      {
        expr_listt new_tuple(sub_tuple);
        new_tuple.emplace_front(elem);
        result.insert(new_tuple);
      }
    }
  }
  return result;
}

std::list<partitiont>
get_partitions_long(const std::size_t n, const std::size_t k)
{
  std::list<partitiont> result;
  // Cuts are an increasing vector of distinct indexes between 0 and n.
  // Note that cuts[0] is always 0 and cuts[k+1] is always n.
  // There is a bijection between partitions and cuts, i.e., for a given cuts,
  // (cuts[1]-cuts[0], cuts[2]-cuts[1], ..., cuts[k+1]-cuts[k])
  // is a partition of n into k components.
  std::vector<std::size_t> cuts;

  // Initialize cuts as (0, n-k+1, n-k+2, ..., n).
  // O: elements
  // |: cuts
  // Initial cuts
  // 000...0111...1
  // So the first partition is (n-k+1, 1, 1, ..., 1).
  cuts.emplace_back(0);
  cuts.emplace_back(n - k + 1);
  for(std::size_t i = 0; i < k - 1; i++)
  {
    cuts.emplace_back(n - k + 2 + i);
  }

  // Done when all cuts were enumerated.
  bool done = false;

  while(!done)
  {
    // Construct a partition from cuts using the bijection described above.
    partitiont new_partition = partitiont();
    for(std::size_t i = 1; i < k + 1; i++)
    {
      new_partition.emplace_back(cuts[i] - cuts[i - 1]);
    }

    // We move to the next cuts. The idea is that
    // 1. we first find the largest index i such that there are space before
    //    cuts[i] where cuts[i] can be moved to;
    //    The index i is the rightmost index we move in this iteration.
    // 2. we then move cuts[i] to its left by 1;
    // 3. move all cuts next to cuts[rightmost_to_move].
    //
    // O: filler
    // |: cuts
    //
    // Example:
    //   Before moving:
    // 00000010010111110
    //            ^
    //      rightmost_to_move
    std::size_t rightmost_to_move = 0;
    for(std::size_t i = 1; i < k; i++)
    {
      if(cuts[i] - cuts[i - 1] > 1)
      {
        rightmost_to_move = i;
      }
    }

    // Move cuts[rightmost_to_move] to its left:
    // 00000010011011110
    //           ^
    //    rightmost_to_move
    cuts[rightmost_to_move] = cuts[rightmost_to_move] - 1;

    // No cut can be moved---we have enumerated all cuts.
    if(rightmost_to_move == 0)
      done = true;
    else
    {
      // Move all cuts (except for cuts[0]) after rightmost_to_move to their
      // rightmost.
      // 00000010011001111
      //           ^
      //    rightmost_to_move
      std::size_t accum = 1;
      for(std::size_t i = k - 1; i > rightmost_to_move; i--)
      {
        cuts[i] = n - accum;
        accum++;
      }
    }
    result.emplace_back(new_partition);
  }
  return result;
}

/// Compute all positions of ones in the bit vector `v` (1-indexed).
std::vector<std::size_t> get_ones_pos(std::size_t v)
{
  const std::size_t length = sizeof(std::size_t) * 8;
  std::vector<std::size_t> result;

  // Start from the lowest bit at position `length`
  std::size_t curr_pos = length;
  while(v != 0)
  {
    if(v % 2)
    {
      result.insert(result.begin(), curr_pos);
    }

    // Move to the next bit.
    v = v >> 1;
    curr_pos--;
  }

  return result;
}

/// Construct parition of `n` elements from a bit vector `v`.
/// For a bit vector with ones at positions (computed by `get_ones_pos`)
/// (ones[0], ones[1], ..., ones[k-2]),
/// the corresponding partition is
/// (ones[0], ones[1]-ones[0], ..., ones[k-2]-ones[k-3], n-ones[k-2]).
partitiont from_bits_to_partition(std::size_t v, std::size_t n)
{
  const std::vector<std::size_t> ones_pos = get_ones_pos(v);

  INVARIANT(ones_pos.size() >= 1, "There should be at least one bit set in v");

  partitiont result = {ones_pos[0]};

  for(std::size_t i = 1; i < ones_pos.size(); i++)
  {
    result.emplace_back(ones_pos[i] - ones_pos[i - 1]);
  }
  result.emplace_back(n - ones_pos[ones_pos.size() - 1]);

  return result;
}

std::list<partitiont> non_leaf_enumeratort::get_partitions(
  const std::size_t n,
  const std::size_t k) const
{
  // Every component should contain at least one element.
  if(n < k)
    return {};

  // Number of bits at all.
  const std::size_t length = sizeof(std::size_t) * 8;

  // This bithack-based implementation works only for `n` no larger than
  // `length`. Use the vector-based implementation `n` is too large.
  if(n > length)
    return get_partitions_long(n, k);

  // We enumerate all bit vectors `v` with k-1 one's such that each component
  // corresponds to one unique partition.
  // For a bit vector with ones at positions (computed by `get_ones_pos`)
  // (ones[0], ones[1], ..., ones[k-2]),
  // the corresponding partition is
  // (ones[0], ones[1]-ones[0], ..., ones[k-2]-ones[k-3], n-ones[k-2]).

  // Initial `v` is with ones at positions (n-k+1, n-k+2, ..., n-2, n-1).
  std::size_t v = 0;
  // Initial `end` (the last bit vectorr we enumerate) is with ones at
  // positions (1, 2, 3, ..., k-1).
  std::size_t end = 0;
  for(size_t i = 0; i < k - 1; i++)
  {
    v++;
    v = v << 1;
    end++;
    end = end << 1;
  }
  v = v << (length - n);
  end = end << (length - k);

  std::list<partitiont> result;
  while(v != end)
  {
    // Construct the partition for current bit vector and add it to `result`
    result.emplace_back(from_bits_to_partition(v, n));

    // https://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
    // Compute the lexicographically next bit permutation.
    std::size_t t = (v | (v - 1)) + 1;
    v = t | ((((t & -t) / (v & -v)) >> 1) - 1);
  }
  result.emplace_back(from_bits_to_partition(v, n));

  return result;
}

bool binary_functional_enumeratort::is_commutative(const irep_idt &op) const
{
  return op_id == ID_equal || op_id == ID_plus || op_id == ID_notequal ||
         op_id == ID_or || op_id == ID_and || op_id == ID_xor ||
         op_id == ID_bitand || op_id == ID_bitor || op_id == ID_bitxor ||
         op_id == ID_mult;
}

bool binary_functional_enumeratort::is_equivalence_class_representation(
  const expr_listt &exprs) const
{
  std::stringstream left, right;
  left << format(exprs.front());
  right << format(exprs.back());
  // When the two sub-enumerators are exchangeable---they enumerate the same
  // set of expressions---, and the operator is commutative, `exprs` is a
  // representation if its sub-expressions are sorted.
  if(is_exchangeable && is_commutative(op_id) && left.str() > right.str())
  {
    return false;
  }

  /// We are not sure if `exprs` is represented by some other tuple.
  return true;
}

exprt binary_functional_enumeratort::instantiate(const expr_listt &exprs) const
{
  INVARIANT(
    exprs.size() == 2,
    "number of arguments should be 2: " + integer2string(exprs.size()));
  if(op_id == ID_equal)
    return equal_exprt(exprs.front(), exprs.back());
  if(op_id == ID_le)
    return less_than_or_equal_exprt(exprs.front(), exprs.back());
  if(op_id == ID_lt)
    return less_than_exprt(exprs.front(), exprs.back());
  if(op_id == ID_gt)
    return greater_than_exprt(exprs.front(), exprs.back());
  if(op_id == ID_ge)
    return greater_than_or_equal_exprt(exprs.front(), exprs.back());
  if(op_id == ID_and)
    return and_exprt(exprs.front(), exprs.back());
  if(op_id == ID_or)
    return or_exprt(exprs.front(), exprs.back());
  if(op_id == ID_plus)
    return plus_exprt(exprs.front(), exprs.back());
  if(op_id == ID_minus)
    return minus_exprt(exprs.front(), exprs.back());
  if(op_id == ID_notequal)
    return notequal_exprt(exprs.front(), exprs.back());
  return binary_exprt(exprs.front(), op_id, exprs.back());
}

expr_sett alternatives_enumeratort::enumerate(const std::size_t size) const
{
  expr_sett result;
  for(const auto &enumerator : sub_enumerators)
  {
    for(const auto &e : enumerator->enumerate(size))
    {
      result.insert(e);
    }
  }
  return result;
}

expr_sett
recursive_enumerator_placeholdert::enumerate(const std::size_t size) const
{
  const auto &it = factory.productions_map.find(identifier);
  INVARIANT(it != factory.productions_map.end(), "No nonterminal found.");
  alternatives_enumeratort actual_enumerator(it->second, ns);
  return actual_enumerator.enumerate(size);
}

void enumerator_factoryt::add_placeholder(
  const recursive_enumerator_placeholdert &placeholder)
{
  // The new placeholder (nonterminal) belongs to this factory (grammar).
  const auto &ret = nonterminal_set.insert(placeholder.identifier);
  INVARIANT(ret.second, "Duplicated non-terminals");
}

void enumerator_factoryt::attach_productions(
  const std::string &id,
  const enumeratorst &enumerators)
{
  const auto &ret = productions_map.insert({id, enumerators});
  INVARIANT(
    ret.second, "Cannnot attach enumerators to a non-existing nonterminal.");
}
