/*******************************************************************\

Module: Dump Goto-Program as DOT Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dump Goto-Program as DOT Graph

#include "dot.h"

#include <sstream>

#include <goto-programs/goto_model.h>

#include <langapi/language_util.h>

#define DOTGRAPHSETTINGS  "color=black;" \
                          "orientation=portrait;" \
                          "fontsize=20;"\
                          "compound=true;"\
                          "size=\"30,40\";"\
                          "ratio=compress;"

class dott
{
public:
  explicit dott(
    const goto_modelt &_goto_model):
    goto_model(_goto_model),
    subgraphscount(0)
  {
  }

  void output(std::ostream &out);

protected:
  const goto_modelt &goto_model;

  unsigned subgraphscount;

  std::list<std::pair<std::string, exprt>> function_calls;
  std::list<exprt> clusters;

  void
  write_dot_subgraph(std::ostream &, const irep_idt &, const goto_programt &);

  void do_dot_function_calls(std::ostream &);

  std::string &escape(std::string &str);

  void write_edge(std::ostream &,
                  const goto_programt::instructiont &,
                  const goto_programt::instructiont &,
                  const std::string &);

  void find_next(const goto_programt::instructionst &,
                 const goto_programt::const_targett &,
                 std::set<goto_programt::const_targett> &,
                 std::set<goto_programt::const_targett> &);
};

/// Write the dot graph that corresponds to the goto program to the output
/// stream.
/// \param out: output stream
/// \param function_id: name of \p goto_program
/// \param goto_program: goto program the dot graph of which is written
void dott::write_dot_subgraph(
  std::ostream &out,
  const irep_idt &function_id,
  const goto_programt &goto_program)
{
  clusters.push_back(exprt("cluster"));
  clusters.back().set("name", function_id);
  clusters.back().set("nr", subgraphscount);

  out << "subgraph \"cluster_" << function_id << "\" {\n";
  out << "label=\"" << function_id << "\";\n";

  const goto_programt::instructionst &instructions =
    goto_program.instructions;

  if(instructions.empty())
  {
    out << "Node_" << subgraphscount << "_0 " <<
      "[shape=Mrecord,fontsize=22,label=\"?\"];\n";
  }
  else
  {
    const namespacet ns(goto_model.symbol_table);

    std::set<goto_programt::const_targett> seen;
    goto_programt::const_targetst worklist;
    worklist.push_back(instructions.begin());

    while(!worklist.empty())
    {
      goto_programt::const_targett it=worklist.front();
      worklist.pop_front();

      if(it==instructions.end() ||
         seen.find(it)!=seen.end()) continue;

      std::stringstream tmp;
      if(it->is_goto())
      {
        if(it->condition().is_true())
          tmp.str("Goto");
        else
        {
          std::string t = from_expr(ns, function_id, it->condition());
          while(t[ t.size()-1 ]=='\n')
            t = t.substr(0, t.size()-1);
          tmp << escape(t) << "?";
        }
      }
      else if(it->is_assume())
      {
        std::string t = from_expr(ns, function_id, it->condition());
        while(t[ t.size()-1 ]=='\n')
          t = t.substr(0, t.size()-1);
        tmp << "Assume\\n(" << escape(t) << ")";
      }
      else if(it->is_assert())
      {
        std::string t = from_expr(ns, function_id, it->condition());
        while(t[ t.size()-1 ]=='\n')
          t = t.substr(0, t.size()-1);
        tmp << "Assert\\n(" << escape(t) << ")";
      }
      else if(it->is_skip())
        tmp.str("Skip");
      else if(it->is_end_function())
        tmp.str("End of Function");
      else if(it->is_location())
        tmp.str("Location");
      else if(it->is_dead())
        tmp.str("Dead");
      else if(it->is_atomic_begin())
        tmp.str("Atomic Begin");
      else if(it->is_atomic_end())
        tmp.str("Atomic End");
      else if(it->is_function_call())
      {
        const code_function_callt function_call(
          it->call_lhs(), it->call_function(), it->call_arguments());
        std::string t = from_expr(ns, function_id, function_call);
        while(t[ t.size()-1 ]=='\n')
          t = t.substr(0, t.size()-1);
        tmp.str(escape(t));

        std::stringstream ss;
        ss << "Node_" << subgraphscount << "_" << it->location_number;
        function_calls.push_back(
          std::pair<std::string, exprt>(ss.str(), it->call_function()));
      }
      else if(
        it->is_assign() || it->is_decl() || it->is_set_return_value() ||
        it->is_other())
      {
        std::string t = from_expr(ns, function_id, it->code());
        while(t[ t.size()-1 ]=='\n')
          t = t.substr(0, t.size()-1);
        tmp.str(escape(t));
      }
      else if(it->is_start_thread())
        tmp.str("Start of Thread");
      else if(it->is_end_thread())
        tmp.str("End of Thread");
      else if(it->is_throw())
        tmp.str("THROW");
      else if(it->is_catch())
        tmp.str("CATCH");
      else
        tmp.str("UNKNOWN");

      out << "Node_" << subgraphscount << "_" << it->location_number;
      out << " [shape=";
      if(it->is_goto() && !it->condition().is_constant())
        out << "diamond";
      else
        out <<"Mrecord";
      out << ",fontsize=22,label=\"";
      out << tmp.str();
      out << "\"];\n";

      std::set<goto_programt::const_targett> tres;
      std::set<goto_programt::const_targett> fres;
      find_next(instructions, it, tres, fres);

      std::string tlabel;
      std::string flabel;
      if(!fres.empty() && !tres.empty())
      {
        tlabel = "true";
        flabel = "false";
      }

      typedef std::set<goto_programt::const_targett> t;

      for(t::iterator trit=tres.begin();
           trit!=tres.end();
           trit++)
        write_edge(out, *it, **trit, tlabel);
      for(t::iterator frit=fres.begin();
          frit!=fres.end();
          frit++)
        write_edge(out, *it, **frit, flabel);

      seen.insert(it);
      const auto temp=goto_program.get_successors(it);
      worklist.insert(worklist.end(), temp.begin(), temp.end());
    }
  }

  out << "}\n";
  subgraphscount++;
}

void dott::do_dot_function_calls(
  std::ostream &out)
{
  for(const auto &call : function_calls)
  {
    std::list<exprt>::const_iterator cit=clusters.begin();
    for( ; cit!=clusters.end(); cit++)
      if(cit->get("name") == call.second.get(ID_identifier))
        break;

    if(cit!=clusters.end())
    {
      out << call.first
          << " -> "
             "Node_"
          << cit->get("nr") << "_0"
          << " [lhead=\"cluster_" << call.second.get(ID_identifier) << "\","
          << "color=blue];\n";
    }
    else
    {
      out << "subgraph \"cluster_" << call.second.get(ID_identifier)
          << "\" {\n";
      out << "rank=sink;\n";
      out << "label=\"" << call.second.get(ID_identifier) << "\";\n";
      out << "Node_" << subgraphscount << "_0 " <<
        "[shape=Mrecord,fontsize=22,label=\"?\"];\n";
      out << "}\n";
      clusters.push_back(exprt("cluster"));
      clusters.back().set("name", call.second.get(ID_identifier));
      clusters.back().set("nr", subgraphscount);
      out << call.first
          << " -> "
             "Node_"
          << subgraphscount << "_0"
          << " [lhead=\"cluster_" << call.second.get("identifier") << "\","
          << "color=blue];\n";
      subgraphscount++;
    }
  }
}

void dott::output(std::ostream &out)
{
  out << "digraph G {\n";
  out << DOTGRAPHSETTINGS << '\n';

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(gf_entry.second.body_available())
      write_dot_subgraph(out, gf_entry.first, gf_entry.second.body);
  }

  do_dot_function_calls(out);

  out << "}\n";
}

/// Escapes a string. beware, this might not work for all kinds of strings.
/// \param str: a string
/// \return the escaped string
std::string &dott::escape(std::string &str)
{
  for(std::string::size_type i=0; i<str.size(); i++)
  {
    if(str[i]=='\n')
    {
      str[i] = 'n';
      str.insert(i, "\\");
    }
    else if(str[i]=='\"' ||
            str[i]=='|' ||
            str[i]=='\\' ||
            str[i]=='>' ||
            str[i]=='<' ||
            str[i]=='{' ||
            str[i]=='}')
    {
      str.insert(i, "\\");
      i++;
    }
  }

  return str;
}

/// finds an instructions successors (for goto graphs)
/// \par parameters: instructions, instruction iterator, true results and
/// false results
void dott::find_next(
  const goto_programt::instructionst &instructions,
  const goto_programt::const_targett &it,
  std::set<goto_programt::const_targett> &tres,
  std::set<goto_programt::const_targett> &fres)
{
  if(it->is_goto() && !it->condition().is_false())
  {
    for(const auto &target : it->targets)
      tres.insert(target);
  }

  if(it->is_goto() && it->condition().is_true())
    return;

  goto_programt::const_targett next = it; next++;
  if(next!=instructions.end())
    fres.insert(next);
}

/// writes an edge from the from node to the to node and with the given label to
/// the output stream (dot format)
/// \par parameters: output stream, from, to and a label
void dott::write_edge(
  std::ostream &out,
  const goto_programt::instructiont &from,
  const goto_programt::instructiont &to,
  const std::string &label)
{
  out << "Node_" << subgraphscount << "_" << from.location_number;
  out << " -> ";
  out << "Node_" << subgraphscount << "_" << to.location_number << " ";
  if(!label.empty())
  {
    out << "[fontsize=20,label=\"" << label << "\"";
    if(from.is_backwards_goto() && from.location_number > to.location_number)
      out << ",color=red";
    out << "]";
  }
  out << ";\n";
}

void dot(const goto_modelt &src, std::ostream &out)
{
  dott dot(src);
  dot.output(out);
}
