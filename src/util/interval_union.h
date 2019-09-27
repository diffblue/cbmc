/*******************************************************************\

Module: Util

Author: Diffblue Limited

\*******************************************************************/

/// \file
/// Union of intervals

#ifndef CPROVER_UTIL_INTERVAL_UNION_H
#define CPROVER_UTIL_INTERVAL_UNION_H

#include <util/interval_template.h>
#include <util/mp_arith.h>
#include <util/nodiscard.h>
#include <util/optional.h>
#include <vector>

class exprt;

/// Represents a set of integers by a union of intervals, which are stored in
/// increasing order for efficient union and intersection (linear time in both
/// cases).
class interval_uniont
{
public:
  using intervalt = interval_templatet<mp_integer>;

  /// Empty union
  interval_uniont() = default;

  /// Set of all integers
  static interval_uniont all_integers();

  /// Construct interval_uniont object representing the set of integers that are
  /// greater or equal to \p value.
  static interval_uniont greater_or_equal(const mp_integer &value);

  /// Construct interval_uniont object representing the set of integers that are
  /// greater or equal to \p value.
  static interval_uniont smaller_or_equal(const mp_integer &value);

  /// Return a new interval_uniontt object representing the set of intergers in
  /// the intersection of this object and \p other.
  NODISCARD interval_uniont
  make_intersection(const interval_uniont &other) const;

  /// Return a new interval_uniontt object representing the set of intergers in
  /// the union of this object and \p other.
  NODISCARD interval_uniont make_union(const interval_uniont &other) const;

  bool is_empty() const;

  /// empty optional means either unbounded on the right or empty,
  /// \ref is_empty has to be called to distinguish between the two
  optionalt<mp_integer> maximum() const;

  /// empty optional means either unbounded on the left or empty,
  /// \ref is_empty has to be called to distinguish between the two
  optionalt<mp_integer> minimum() const;

  /// Convert the set to a string representing a sequence of intervals, each
  /// interval being of the form "[lower:upper]", "[:upper]" if there is no
  /// lower bound, "[lower:]" if there is no upper bound, "[:]" for the whole
  /// set of integers and "[]" for the empty set.
  std::string to_string() const;

  /// Parse a string which is a comma `,` separated list of intervals of the
  /// form "[lower1:upper1]", for example: "[-3:-2],[4:5]".
  /// Return an empty optional if the string doesn't match the format.
  static optionalt<interval_uniont> of_string(const std::string &to_parse);

  /// Construct interval union from a single interval
  static interval_uniont of_interval(intervalt interval);

  /// Expression which is true exactly when \p e belongs to the set.
  exprt make_contains_expr(const exprt &e) const;

  /// If the set contains only one element, return the value of this element.
  optionalt<mp_integer> as_singleton() const;

private:
  /// Non-overlapping intervals stored in order of their lower bound, so that
  /// each interval is strictly below the following one.
  /// As a consequence an interval without a lower-bound can only occur in first
  /// position and one without an upper-bound in last position.
  std::vector<intervalt> intervals;

  /// Check that intervals are strictly ordered.
  bool validate() const;
};

#endif // CPROVER_UTIL_INTERVAL_UNION_H
