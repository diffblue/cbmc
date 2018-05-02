/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#include "static_show_domain.h"

#include <util/options.h>

#include <analyses/dependence_graph.h>

/// Runs the analyzer and then prints out the domain
/// \param goto_model: the program analyzed
/// \param ai: the abstract interpreter after it has been run to fix point
/// \param options: the parsed user options
/// \param message_handler: the system message handler
/// \param out: output stream for the printing
/// \return: false on success with the domain printed to out
bool static_show_domain(
  const goto_modelt &goto_model,
  const ai_baset &ai,
  const optionst &options,
  message_handlert &message_handler,
  std::ostream &out)
{
  if(options.get_bool_option("json"))
  {
    out << ai.output_json(goto_model);
  }
  else if(options.get_bool_option("xml"))
  {
    out << ai.output_xml(goto_model);
  }
  else if(options.get_bool_option("dot") &&
          options.get_bool_option("dependence-graph"))
  {
    const dependence_grapht *d=dynamic_cast<const dependence_grapht*>(&ai);
    INVARIANT(d!=nullptr,
              "--dependence-graph sets ai to be a dependence_graph");

    out << "digraph g {\n";
    d->output_dot(out);
    out << "}\n";
  }
  else
  {
    INVARIANT(options.get_bool_option("text"), "Other output formats handled");
    ai.output(goto_model, out);
  }

  return false;
}
