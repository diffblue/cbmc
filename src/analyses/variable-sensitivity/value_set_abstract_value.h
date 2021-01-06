/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-value-set

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Value sets for primitives

// NOLINTNEXTLINE(whitespace/line_length)
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_VALUE_H
// NOLINTNEXTLINE(whitespace/line_length)
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_VALUE_H

#include <analyses/variable-sensitivity/abstract_object.h>

#include <unordered_set>

class value_set_abstract_valuet : public abstract_objectt
{
public:
  using valuest = std::unordered_set<exprt, irep_hash>;

  explicit value_set_abstract_valuet(
    const typet &type,
    bool top = true,
    bool bottom = false);
  value_set_abstract_valuet(
    exprt expr,
    const abstract_environmentt &environment,
    const namespacet &ns);
  value_set_abstract_valuet(const typet &type, valuest values);

  /// Get the possible values for this abstract object.
  /// Only meaningful when this is neither TOP nor BOTTOM.
  const valuest &get_values() const;

  CLONE

  /// TODO arbitrary limit, make configurable
  static constexpr std::size_t max_value_set_size = 10;

  exprt to_constant() const override;

  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  void output(std::ostream &out, const class ai_baset &ai, const namespacet &ns)
    const override;

protected:
  abstract_object_pointert merge(abstract_object_pointert other) const override;

private:
  /// If BOTTOM then empty.
  /// If neither BOTTOM or TOP then the exact set of values.
  /// If TOP this field doesn't mean anything and shouldn't be looked at.
  valuest values;
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_VALUE_H
