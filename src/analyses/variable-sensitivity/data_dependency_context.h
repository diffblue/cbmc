/*******************************************************************\

Module: analyses variable-sensitivity data_dependency_context

Author: Diffblue Ltd

\*******************************************************************/

/**
 * \file
 * Maintain data dependencies as a context in the variable sensitivity domain
 */

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_DATA_DEPENDENCY_CONTEXT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_DATA_DEPENDENCY_CONTEXT_H

#include "variable_sensitivity_domain.h"
#include "write_location_context.h"

class data_dependency_contextt:
  public write_location_contextt {
public:
  // These constructors mirror those in the base abstract_objectt, but with
  // the addition of an extra argument which is the abstract_objectt to wrap.
  explicit data_dependency_contextt(
    const abstract_object_pointert child,
    const typet &type):
      write_location_contextt(child, type)
  {
  }

  data_dependency_contextt(
    const abstract_object_pointert child,
    const typet &type,
    bool top,
    bool bottom):
      write_location_contextt(child, type, top, bottom)
  {
  }

  explicit data_dependency_contextt(
    const abstract_object_pointert child,
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns):
      write_location_contextt(child, expr, environment, ns)
  {
  }

  virtual abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const exprt &specifier,
    const abstract_object_pointert value,
    bool merging_write) const override;

  virtual abstract_object_pointert update_location_context(
    const abstract_objectt::locationst &locations,
    const bool update_sub_elements) const override;

  bool has_been_modified(const abstract_object_pointert before) const override;

  std::set<goto_programt::const_targett> get_data_dependencies() const;
  std::set<goto_programt::const_targett> get_data_dominators() const;

  virtual void output(
    std::ostream &out, const class ai_baset &ai, const namespacet &ns) const
  override;

protected:
  CLONE

  virtual abstract_object_pointert merge(
    abstract_object_pointert other) const override;

  virtual abstract_object_pointert abstract_object_merge_internal(
    const abstract_object_pointert other) const override;


private:
  class location_ordert
  {
  public:
    bool operator()(
      goto_programt::const_targett instruction,
      goto_programt::const_targett other_instruction)
    {
      return instruction->location_number>
             other_instruction->location_number;
    }
  };
  typedef std::set<goto_programt::const_targett, location_ordert> dependencest;
  dependencest data_deps;
  dependencest data_dominators;

  abstract_object_pointert insert_data_deps(
    const dependencest &dependencies) const;

  abstract_object_pointert insert_data_deps(const locationst &locations) const
  {
    // `locationst` is unsorted, so convert this to a sorted `dependenciest`
    dependencest dependencies;

    for(const auto l : locations)
      dependencies.insert(l);

    return insert_data_deps(dependencies);
  }

};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_DATA_DEPENDENCY_CONTEXT_H
