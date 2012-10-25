/*******************************************************************\

Module: Dump Goto-Program as DOT Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <fstream>
#include <sstream>

#define DOTGRAPHSETTINGS  "color=black;" \
                          "orientation=portrait;" \
                          "fontsize=20;"\
                          "compound=true;"\
                          "size=\"30,40\";"\
                          "ratio=compress;"

#include "dot.h"

class dott
{
public:
  dott(
    const goto_functionst &_goto_functions,
    const namespacet &_ns):
    ns(_ns),
    goto_functions(_goto_functions),
    subgraphscount(0)
  {
  }
  
  void output(std::ostream &out);
  
protected:
  const namespacet &ns;
  const goto_functionst &goto_functions;

  unsigned subgraphscount;

  std::list<exprt> function_calls;
  std::list<exprt> clusters;

  void write_dot_subgraph(
    std::ostream &, 
    const std::string &, 
    const goto_programt &);
    
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

/*******************************************************************\

Function: dott::write_dot_subgraph

  Inputs: output stream, name and goto program

 Outputs: true on error, false otherwise

 Purpose: writes the dot graph that corresponds to the goto program
          to the output stream.

\*******************************************************************/

void dott::write_dot_subgraph(
  std::ostream &out,
  const std::string &name,
  const goto_programt &goto_program)
{
  clusters.push_back(exprt("cluster"));
  clusters.back().set("name", name);
  clusters.back().set("nr", subgraphscount);

  out << "subgraph \"cluster_" << name << "\" {" << std::endl;
  out << "label=\"" << name << "\";" << std::endl;

  const goto_programt::instructionst& instructions =
    goto_program.instructions;  
  
  if(instructions.size()==0)
  {
    out << "Node_" << subgraphscount << "_0 " <<
      "[shape=Mrecord,fontsize=22,label=\"?\"];" << std::endl;
  }
  else
  {
    std::set<goto_programt::const_targett> seen;
    goto_programt::const_targetst worklist;
    worklist.push_back(instructions.begin());
    
    while(!worklist.empty())
    {
      goto_programt::const_targett it=worklist.front();
      worklist.pop_front();
      
      if(it==instructions.end() ||
         seen.find(it)!=seen.end()) continue;
          
      std::stringstream tmp("");
      if(it->is_goto())
      {
        if(it->guard.is_true())
          tmp.str("Goto");
        else
        {
          std::string t = from_expr(ns, "", it->guard);
          while (t[ t.size()-1 ]=='\n')
            t = t.substr(0,t.size()-1);
          tmp << escape(t) << "?";
        }
      }
      else if(it->is_assume())
      {
        std::string t = from_expr(ns, "", it->guard);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
        tmp << "Assume\\n(" << escape(t) << ")";
      }
      else if(it->is_assert())
      {
        std::string t = from_expr(ns, "", it->guard);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
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
        std::string t = from_expr(ns, "", it->code);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
        tmp.str(escape(t));
        
        exprt fc;
        std::stringstream ss;
        ss << "Node_" << subgraphscount << "_" << it->location_number;
        fc.operands().push_back(exprt(ss.str()));
        fc.operands().push_back(it->code.op1());  
        function_calls.push_back(fc);
      }
      else if(it->is_assign() ||
               it->is_return() ||
               it->is_other())      
      {
        std::string t = from_expr(ns, "", it->code);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
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
      if(it->is_goto() && !it->guard.is_true() && !it->guard.is_false())
        out << "diamond";
      else
        out <<"Mrecord";
      out << ",fontsize=22,label=\"";
      out << tmp.str();
      out << "\"];" << std::endl;

      std::set<goto_programt::const_targett> tres;
      std::set<goto_programt::const_targett> fres;          
      find_next(instructions, it, tres, fres);

      std::string tlabel="true";
      std::string flabel="false";
      if(fres.size()==0 || tres.size()==0)
      {
        tlabel="";
        flabel="";
      }
            
      typedef std::set<goto_programt::const_targett> t;          
      
      for (t::iterator trit=tres.begin();
           trit!=tres.end();
           trit++)
        write_edge(out, *it, **trit, tlabel);
      for (t::iterator frit=fres.begin();
          frit!=fres.end();
          frit++)
        write_edge(out, *it, **frit, flabel);
    
      seen.insert(it);
      goto_programt::const_targetst temp;
      goto_program.get_successors(it, temp);
      worklist.insert(worklist.end(), temp.begin(), temp.end());
    }
  }
  
  out << "}" << std::endl;
  subgraphscount++;
}

/*******************************************************************\

Function: dott::do_dot_function_calls

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dott::do_dot_function_calls(
  std::ostream &out)
{
  for(std::list<exprt>::const_iterator
      it=function_calls.begin();
      it!=function_calls.end();
      it++)
  {
    std::list<exprt>::const_iterator cit=clusters.begin();
    for(;cit!=clusters.end();cit++)
      if(cit->get("name")==it->op1().get(ID_identifier))
        break;

    if(cit!=clusters.end())
    {
      out << it->op0().id() <<
        " -> " "Node_" << cit->get("nr") << "_0" <<
        " [lhead=\"cluster_" << it->op1().get(ID_identifier) << "\"," <<
        "color=blue];" << std::endl;
    }
    else
    {
      out << "subgraph \"cluster_" << it->op1().get(ID_identifier) <<
        "\" {" << std::endl;
      out << "rank=sink;"<<std::endl;
      out << "label=\"" << it->op1().get(ID_identifier) << "\";" << std::endl;
      out << "Node_" << subgraphscount << "_0 " <<
        "[shape=Mrecord,fontsize=22,label=\"?\"];"
          << std::endl;
      out << "}" << std::endl;
      clusters.push_back(exprt("cluster"));
      clusters.back().set("name", it->op1().get(ID_identifier));
      clusters.back().set("nr", subgraphscount);
      out << it->op0().id() <<
        " -> " "Node_" << subgraphscount << "_0" <<
        " [lhead=\"cluster_" << it->op1().get("identifier") << "\"," <<
        "color=blue];" << std::endl;
      subgraphscount++;
    }
  }
}

/*******************************************************************\

Function: dott::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dott::output(std::ostream &out)
{
  out << "digraph G {" << std::endl;
  out << DOTGRAPHSETTINGS << std::endl;

  std::list<exprt> clusters;

  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
  {
    if(it->second.body_available)
      write_dot_subgraph(out, id2string(it->first), it->second.body);
  }

  do_dot_function_calls(out);

  out << "}" << std::endl;
}

/*******************************************************************\

Function: dott::escape

  Inputs: a string

 Outputs: the escaped string

 Purpose: escapes a string. beware, this might not work for all
          kinds of strings.

\*******************************************************************/

std::string &dott::escape(std::string &str)
{
  for(unsigned i=0; i<str.size(); i++)
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

/*******************************************************************\

Function: dott::find_next

  Inputs: instructions, instruction iterator, true results and
          false results

 Outputs: none

 Purpose: finds an instructions successors (for goto graphs)

\*******************************************************************/

void dott::find_next(
  const goto_programt::instructionst &instructions,
  const goto_programt::const_targett &it,
  std::set<goto_programt::const_targett> &tres,
  std::set<goto_programt::const_targett> &fres)
{
  if(it->is_goto() && !it->guard.is_false())
  {
    goto_programt::targetst::const_iterator gtit = it->targets.begin();
    for (; gtit!=it->targets.end(); gtit++)
      tres.insert((*gtit));
  }

  if(it->is_goto() && it->guard.is_true())
    return;
  
  goto_programt::const_targett next = it; next++;
  if(next!=instructions.end())
    fres.insert(next);
}

/*******************************************************************\

Function: dott::write_edge

  Inputs: output stream, from, to and a label

 Outputs: none

 Purpose: writes an edge from the from node to the to node and with
          the given label to the output stream (dot format)

\*******************************************************************/

void dott::write_edge(
  std::ostream &out,
  const goto_programt::instructiont &from,
  const goto_programt::instructiont &to,
  const std::string &label)
{
  out << "Node_" << subgraphscount << "_" << from.location_number;
  out << " -> ";
  out << "Node_" << subgraphscount << "_" << to.location_number << " ";
  if(label!="")
    {
      out << "[fontsize=20,label=\"" << label << "\"";
      if(from.is_backwards_goto() &&
          from.location_number > to.location_number)
        out << ",color=red";
      out << "]";
    }
  out << ";" << std::endl;
}

/*******************************************************************\

Function: dot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dot(
  const goto_functionst &src,
  const namespacet &ns,
  std::ostream &out)
{
  dott dot(src, ns);
  dot.output(out);  
}

