/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-dependence-graph

 Author: Diffblue Ltd.

\*******************************************************************/

#include "data_dependency_context.h"
#include "variable_sensitivity_dependence_graph.h"

#include <langapi/language_util.h>
#include <util/json.h>
#include <util/json_expr.h>


/**
 * Evaluate an expression and accumulate all the data dependencies
 * involved in the evaluation.
 *
 * \param expr the expression to evaluate
 * \param ns the namespace to use
 * \param deps the destination in which to accumlate data dependencies
 */
void variable_sensitivity_dependence_grapht::eval_data_deps(
  const exprt &expr, const namespacet &ns, data_depst &deps) const
{
  const auto res=
    std::dynamic_pointer_cast<const data_dependency_contextt>(eval(expr, ns));

  if(res->get_data_dependencies().size() > 0)
  {
    // If the expression was able to be eval'ed to something with data
    // dependencies, then that's all we need to gather.
    for (const auto dep : res->get_data_dependencies())
      deps.insert(dep);
  }
  else
  {
    // If the expression could not be eval'ed to somethign with data
    // dependencies, then it may have been some sort of compound expression,
    // so attempt to eval the data dependencies for all the operands, taking
    // the union of them all.
    for(const exprt &op : expr.operands())
    {
      eval_data_deps(op, ns, deps);
    }
  }
}

/**
 * Compute the abstract transformer for a single instruction. For
 * the data dependencies, this involves calculating all the data
 * dependencies that exist in the 'to' instruction.
 *
 * \param from the instruction before the abstract domain
 * \param to the instruction after the abstract domain
 * \param ai the abstract interpreter
 * \param ns the namespace
 */
void variable_sensitivity_dependence_grapht::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
   const namespacet &ns)
{
  variable_sensitivity_domaint::transform(from, to, ai, ns);

  // Find all the data dependencies in the the 'to' expression
  domain_data_deps.clear();
  if(to->is_assign())
  {
    const code_assignt &inst = to_code_assign(to->code);

    eval_data_deps(inst.rhs(), ns, domain_data_deps);
  }
}

/**
 * Computes the join between "this" and "b"
 *
 * \param b the other domain
 * \param from the location preceding the 'b' domain
 * \param to the current location
 * \return true if something has changed in the merge
 */
bool variable_sensitivity_dependence_grapht::merge(
    const variable_sensitivity_domaint &b,
    locationt from,
    locationt to)
{
  bool changed = false;

  changed = variable_sensitivity_domaint::merge(b, from, to);

  const auto cast_b =
    dynamic_cast<const variable_sensitivity_dependence_grapht&>(b);

  for (auto bdep : cast_b.domain_data_deps)
  {
    auto result = domain_data_deps.insert(bdep);
    changed |= result.second;
  }

  return changed;
}

/**
 * Perform a context aware merge of the changes that have been applied
 * between function_start and the current state. Anything that has not been
 * modified will be taken from the \p function_call domain.
 *
 * \param function_call: The local of the merge - values from here will be
 *   taken if they have not been modified
 * \param function_start: THe base of the merge - changes that have been made
 *   between here and this will be retained.
 * \param ns: The global namespace
 */
void variable_sensitivity_dependence_grapht::merge_three_way_function_return(
  const ai_domain_baset &function_call,
  const ai_domain_baset &function_start,
  const ai_domain_baset &function_end,
  const namespacet &ns)
{
  // The gathering of the data dependencies for the domain is handled by the
  // 'transform' and simply relies on the underlying domains with their
  // data_dependency_context to be correct. Therefore all we need to ensure at
  // the three way merge is that the underlying variable senstivitiy domain 
  // does it's three way merge.
  variable_sensitivity_domaint::merge_three_way_function_return(
    function_call,
    function_start,
    function_end,
    ns);
}

/**
 * Basic text output of the abstract domain
 *
 * \param out the stream to output onto
 * \param ai the abstract domain
 * \param ns the namespace
 */
void variable_sensitivity_dependence_grapht::output(
   std::ostream &out,
   const ai_baset &ai,
   const namespacet &ns) const
{
  if(!domain_data_deps.empty())
  {
      out << "Data dependencies: ";
      bool first = true;
      for (auto &dep : domain_data_deps)
      {
        if(!first)
          out << ", ";

        out << dep->location_number;

        first = false;
      }
      out << std::endl;
    }
}

/**
 * \brief Outputs the current value of the domain.
 *
 * \param ai the abstract interpreter
 * \param ns the namespace
 *
 * \return the domain, formatted as a JSON object.
 */
jsont variable_sensitivity_dependence_grapht::output_json(
  const ai_baset &ai,
  const namespacet &ns) const
{
  json_arrayt graph;

  for(const auto &dep : domain_data_deps)
  {
    json_objectt &link=graph.push_back().make_object();
    link["locationNumber"]=
      json_numbert(std::to_string(dep->location_number));
    link["sourceLocation"]=json(dep->source_location);
    json_stringt(dep->source_location.as_string());
    link["type"]=json_stringt("data");
  }

  return graph;
}
