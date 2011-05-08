/*******************************************************************\

Module: Subgoal Documentation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <i2string.h>
#include <ansi-c/expr2c.h>

#include "document_claims.h"

#define MAXWIDTH 62

struct linet
{
  std::string text;
  int line_number;
};

/*******************************************************************\

Function: strip_space

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strip_space(std::list<linet> &lines)
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

Function: emphasize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string emphasize(const std::string &s)
{
  #if 0
  std::string dest;
  bool bold_mode=false;

  for(unsigned i=0; i<s.size(); i++)
  {
    bool new_mode=isalnum(s[i]) ||
                  s[i]=='.' || s[i]==',';

    if(new_mode!=bold_mode)
    {
      if(new_mode)
        dest+="{\\bf{";
      else
        dest+="}}";
      
      bold_mode=new_mode;
    }

    dest+=s[i];
  }

  if(bold_mode)
    dest+="}}";

  return dest;
  #else
  return "{\\ttb{}"+s+"}";
  #endif
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

Function: get_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_code(const irept &location, std::string &dest)
{
  dest="";

  const irep_idt &file=location.get("file");
  const irep_idt &line=location.get("line");

  if(file=="" || line=="") return;

  std::ifstream in(file.c_str());

  if(!in)
  {
    dest+="unable to open ";
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

    while(line_no.size()<4)
      line_no=" "+line_no;

    std::string tmp=line_no+"  "+escape_latex(it->text, true);

    if(it->line_number==line_int)
      tmp=emphasize(tmp);

    dest+=tmp+"\n";
  }
}

/*******************************************************************\

Function: document_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct doc_claimt
{
  std::set<irep_idt> comment_set;
};

void document_claims(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out)
{
  typedef std::map<irept, doc_claimt> claim_sett;
  claim_sett claim_set;

  forall_goto_functions(f_it, goto_functions)
  {
    const goto_programt &goto_program=f_it->second.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_assert())
      {
        locationt new_location;

        new_location.set("file", i_it->location.get("file"));
        new_location.set("line", i_it->location.get("line"));
        new_location.set("function", i_it->location.get("function"));

        claim_set[new_location].comment_set.
          insert(i_it->location.get("comment"));
      }
    }
  }

  for(claim_sett::const_iterator it=claim_set.begin();
      it!=claim_set.end(); it++)
  {
    std::string code;
    const irept &location=it->first;

    get_code(location, code);

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
  }
}
