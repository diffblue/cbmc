/*******************************************************************\

Module:

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <fstream>
#include <memory>

#include <util/message.h>
#include <util/json.h>
#include <util/xml.h>

#include <analyses/interval_domain.h>
#include <analyses/constant_propagator.h>
#include <analyses/dependence_graph.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>

#include "static_show_domain.h"

/// Runs the analyzer and then prints out the domain.
/// \par parameters: The goto_model to analyze, options giving the domain and
///   output,
/// the message handler and output stream.
/// \return The abstract domain via out.
bool static_show_domain(
  const goto_modelt &goto_model,
  const optionst &options,
  message_handlert &message_handler,
  std::ostream &out)
{
  ai_baset *domain=nullptr;

  namespacet ns(goto_model.symbol_table);
  messaget m(message_handler);

  m.status() << "Selecting abstract domain" << messaget::eom;

  if(options.get_bool_option("flow-sensitive"))
  {
    if(options.get_bool_option("constants"))
    {
      domain=
        new constant_propagator_ait(
          goto_model.goto_functions,
          options.get_bool_option("ignore-unresolved-calls"));
    }
    else if(options.get_bool_option("intervals"))
      domain=new ait<interval_domaint>();
    else if(options.get_bool_option("dependence-graph"))
      domain=new dependence_grapht(goto_model.goto_functions, ns);
    else if(options.get_bool_option("variable"))
      domain=new ait<variable_sensitivity_domaint>();
  }
  else if(options.get_bool_option("concurrent"))
  {
    // Constant and interval don't have merge_shared yet
#if 0
    if(options.get_bool_option("constants"))
    domain=new concurrency_aware_ait<constant_propagator_domaint>();

    else if(options.get_bool_option("intervals"))
    domain=new concurrency_aware_ait<interval_domaint>();

    // else if(options.get_bool_option("non-null"))
    //   domain=new concurrency_aware_ait<non_null_domaint>();
#endif
  }

  if(domain==nullptr)
  {
    m.status() << "Task / Interpreter / Domain combination not supported"
               << messaget::eom;
    return true;
  }

  m.status() << "Computing abstract states" << messaget::eom;
  (*domain)(goto_model);

  m.status() << "Outputting abstract states" << messaget::eom;

  if(options.get_bool_option("json"))
    out << domain->output_json(goto_model) << "\n";
  else if(options.get_bool_option("xml"))
    out << domain->output_xml(goto_model) << "\n";
  else if(options.get_bool_option("dot") &&
          options.get_bool_option("dependence-graph"))
  {
    dependence_grapht *d=dynamic_cast<dependence_grapht*>(domain);
    assert(d!=NULL);

    out << "digraph g {\n";
    d->output_dot(out);
    out << "}\n";
  }
  else
    domain->output(goto_model, out);

  delete domain;

  return false;
}
