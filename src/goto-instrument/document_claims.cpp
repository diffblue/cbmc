/*******************************************************************\

Module: Subgoal Documentation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <cstdlib>

#include <i2string.h>
#include <ansi-c/expr2c.h>

#include "document_claims.h"

#define MAXWIDTH 62

class document_claimst
{
public:
  document_claimst(
    const namespacet &_ns,
    const goto_functionst &_goto_functions,
    std::ostream &_out):
    ns(_ns),
    goto_functions(_goto_functions),
    out(_out)
  {
  }
  
  void html()
  {
    format=HTML;
    doit();
  }

  void latex()
  {
    format=LATEX;
    doit();
  }

private:
  const namespacet &ns;
  const goto_functionst &goto_functions;
  std::ostream &out;
    
  struct linet
  {
    std::string text;
    int line_number;
  };

  static void strip_space(std::list<linet> &lines);

  void get_code(
    const locationt &location,
    std::string &dest);
    
  struct doc_claimt
  {
    std::set<irep_idt> comment_set;
  };

  enum { HTML, LATEX } format;
  
  void doit();
};

/*******************************************************************\

Function: document_claimst::strip_space

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void document_claimst::strip_space(std::list<linet> &lines)
{
  unsigned strip=50;

  for(std::list<linet>::const_iterator it=lines.begin();
      it!=lines.end(); it++)
  {
    for(unsigned j=0; j<strip && j<it->text.size(); j++)
      if(it->text[j]!=' ')
      {
        strip=j;
        break;
      }
  }

  if(strip!=0)
  {
    for(std::list<linet>::iterator it=lines.begin();
        it!=lines.end(); it++)
    {
      if(it->text.size()>=strip)
        it->text=std::string(it->text, strip, std::string::npos);

      if(it->text.size()>=MAXWIDTH)
        it->text=std::string(it->text, 0, MAXWIDTH);
    }
  }
}

/*******************************************************************\

Function: escape_latex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string escape_latex(const std::string &s, bool alltt)
{
  std::string dest;

  for(unsigned i=0; i<s.size(); i++)
  {
    if(s[i]=='\\' || s[i]=='{' || s[i]=='}')
      dest+="\\";

    if(!alltt && 
       (s[i]=='_' || s[i]=='$' || s[i]=='~' ||
        s[i]=='^' || s[i]=='%' || s[i]=='#' ||
        s[i]=='&'))
      dest+="\\";

    dest+=s[i];
  }

  return dest;
}

/*******************************************************************\

Function: escape_html

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string escape_html(const std::string &s)
{
  std::string dest;

  for(unsigned i=0; i<s.size(); i++)
  {
    switch(s[i])
    {
    case '&': dest+="&amp;"; break;
    case '<': dest+="&lt;"; break;
    case '>': dest+="&gt;"; break;
    default: dest+=s[i];
    }
  }

  return dest;
}

/*******************************************************************\

Function: is_empty

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_empty(const std::string &s)
{
  for(unsigned i=0; i<s.size(); i++)
    if(isgraph(s[i]))
      return false;

  return true;
}

/*******************************************************************\

Function: document_claimst::get_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void document_claimst::get_code(
  const locationt &location,
  std::string &dest)
{
  dest="";

  const irep_idt &file=location.get_file();
  const irep_idt &line=location.get_line();

  if(file=="" || line=="") return;

  std::ifstream in(file.c_str());

  if(!in)
  {
    dest+="ERROR: unable to open ";
    dest+=id2string(file);
    dest+="\n";
    return;
  }

  int line_int=atoi(line.c_str());

  int line_start=line_int-3,
      line_end=line_int+3;

  if(line_start<=1) line_start=1;

  // skip line_start-1 lines

  for(int l=0; l<line_start-1; l++)
  {
    std::string tmp;
    std::getline(in, tmp);
  }

  // read till line_end

  std::list<linet> lines;

  for(int l=line_start; l<=line_end && in; l++)
  {
    lines.push_back(linet());

    std::string &line=lines.back().text;
    std::getline(in, line);

    if(!line.empty() && line[line.size()-1]=='\r')
      line.resize(line.size()-1);

    lines.back().line_number=l;
  }

  // remove empty lines at the end and at the beginning

  for(std::list<linet>::iterator it=lines.begin();
      it!=lines.end();)
  {
    if(is_empty(it->text))
      it=lines.erase(it);
    else
      break;
  }    

  for(std::list<linet>::iterator it=lines.end();
      it!=lines.begin();)
  {
    it--;

    if(is_empty(it->text))
      it=lines.erase(it);
    else
      break;
  }

  // strip space
  strip_space(lines);

  // build dest

  for(std::list<linet>::iterator it=lines.begin();
      it!=lines.end(); it++)
  {
    std::string line_no=i2string(it->line_number);

    std::string tmp;

    switch(format)
    {
    case LATEX:
      while(line_no.size()<4)
        line_no=" "+line_no;
    
      line_no+"  ";
    
      tmp+=escape_latex(it->text, true);

      if(it->line_number==line_int)
        tmp="{\\ttb{}"+tmp+"}";
        
      break;
      
    case HTML:
      while(line_no.size()<4)
        line_no="&nbsp;"+line_no;
    
      line_no+"&nbsp;&nbsp;";
    
      tmp+=escape_html(it->text);

      if(it->line_number==line_int)
        tmp="<em>"+tmp+"</em>";
        
      break;
    }

    dest+=tmp+"\n";
  }
}

/*******************************************************************\

Function: document_claimst::doit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void document_claimst::doit()
{
  typedef std::map<locationt, doc_claimt> claim_sett;
  claim_sett claim_set;

  forall_goto_functions(f_it, goto_functions)
  {
    const goto_programt &goto_program=f_it->second.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_assert())
      {
        locationt new_location;

        new_location.set_file(i_it->location.get_file());
        new_location.set_line(i_it->location.get_line());
        new_location.set_function(i_it->location.get_function());

        claim_set[new_location].comment_set.
          insert(i_it->location.get_comment());
      }
    }
  }

  for(claim_sett::const_iterator it=claim_set.begin();
      it!=claim_set.end(); it++)
  {
    std::string code;
    const locationt &location=it->first;

    get_code(location, code);

    switch(format)
    {
    case LATEX:
      out << "\\claimlocation{File "
          << escape_latex(location.get_string("file"), false)
          << " function "
          << escape_latex(location.get_string("function"), false)
          << "}" << std::endl;

      out << std::endl;

      for(std::set<irep_idt>::const_iterator
          s_it=it->second.comment_set.begin();
          s_it!=it->second.comment_set.end();
          s_it++)
        out << "\\claim{" << escape_latex(id2string(*s_it), false)
            << "}" << std::endl;

      out << std::endl;

      out << "\\begin{alltt}\\claimcode\n"
          << code
          << "\\end{alltt}\n";

      out << std::endl;
      out << std::endl;
      break;
    
    case HTML:
      out << "<div class=\"claim\">" << std::endl
          << "<div class=\"location\">File "
          << escape_html(location.get_string("file"))
          << " function "
          << escape_html(location.get_string("function"))
          << "</div>" << std::endl;

      out << std::endl;

      for(std::set<irep_idt>::const_iterator
          s_it=it->second.comment_set.begin();
          s_it!=it->second.comment_set.end();
          s_it++)
        out << "<div class=\"description\">" << std::endl
            << escape_html(id2string(*s_it)) << std::endl
            << "</div>" << std::endl;

      out << std::endl;

      out << "<div class=\"code\">\n"
          << code
          << "</div> <!-- code -->" << std::endl;

      out << "</div> <!-- claim -->" << std::endl;
      out << std::endl;
      break;
    }
  }
}

/*******************************************************************\

Function: document_claims_html

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void document_claims_html(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out)
{
  document_claimst(ns, goto_functions, out).html();
}

/*******************************************************************\

Function: document_claims_latex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void document_claims_latex(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out)
{
  document_claimst(ns, goto_functions, out).latex();
}

