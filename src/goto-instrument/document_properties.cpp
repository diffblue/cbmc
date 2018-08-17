/*******************************************************************\

Module: Subgoal Documentation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Subgoal Documentation

#include "document_properties.h"

#include <fstream>

#include <util/string2int.h>

#include <ansi-c/expr2c.h>

#include <goto-programs/goto_model.h>

#define MAXWIDTH 62

class document_propertiest
{
public:
  document_propertiest(
    const goto_functionst &_goto_functions,
    std::ostream &_out):
    goto_functions(_goto_functions),
    out(_out),
    format(HTML)
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
  const goto_functionst &goto_functions;
  std::ostream &out;

  struct linet
  {
    std::string text;
    int line_number;
  };

  static void strip_space(std::list<linet> &lines);

  void get_code(
    const source_locationt &source_location,
    std::string &dest);

  struct doc_claimt
  {
    std::set<irep_idt> comment_set;
  };

  enum { HTML, LATEX } format;

  void doit();
};

void document_propertiest::strip_space(std::list<linet> &lines)
{
  std::size_t strip=50;

  for(const auto &line : lines)
  {
    for(std::size_t j = 0; j < strip && j < line.text.size(); j++)
      if(line.text[j] != ' ')
      {
        strip=j;
        break;
      }
  }

  if(strip!=0)
  {
    for(auto &line : lines)
    {
      if(line.text.size() >= strip)
        line.text = std::string(line.text, strip, std::string::npos);

      if(line.text.size() >= MAXWIDTH)
        line.text = std::string(line.text, 0, MAXWIDTH);
    }
  }
}

std::string escape_latex(const std::string &s, bool alltt)
{
  std::string dest;

  for(auto ch : s)
  {
    if(ch == '\\' || ch == '{' || ch == '}')
      dest+="\\";

    if(
      !alltt && (ch == '_' || ch == '$' || ch == '~' || ch == '^' ||
                 ch == '%' || ch == '#' || ch == '&'))
      dest+="\\";

    dest += ch;
  }

  return dest;
}

std::string escape_html(const std::string &s)
{
  std::string dest;

  for(auto ch : s)
  {
    switch(ch)
    {
    case '&': dest+="&amp;"; break;
    case '<': dest+="&lt;"; break;
    case '>': dest+="&gt;"; break;
    default:
      dest += ch;
    }
  }

  return dest;
}

bool is_empty(const std::string &s)
{
  for(auto ch : s)
    if(isgraph(ch))
      return false;

  return true;
}

void document_propertiest::get_code(
  const source_locationt &source_location,
  std::string &dest)
{
  dest="";

  const irep_idt &file=source_location.get_file();
  const irep_idt &line=source_location.get_line();

  if(file=="" || line=="")
    return;

  std::ifstream in(id2string(file));

  if(!in)
  {
    dest+="ERROR: unable to open ";
    dest+=id2string(file);
    dest+="\n";
    return;
  }

  int line_int=unsafe_string2int(id2string(line));

  int line_start=line_int-3,
      line_end=line_int+3;

  if(line_start<=1)
    line_start=1;

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

  for(const auto &line : lines)
  {
    std::string line_no = std::to_string(line.line_number);

    std::string tmp;

    switch(format)
    {
    case LATEX:
      while(line_no.size()<4)
        line_no=" "+line_no;

      line_no+"  ";

      tmp += escape_latex(line.text, true);

      if(line.line_number == line_int)
        tmp="{\\ttb{}"+tmp+"}";

      break;

    case HTML:
      while(line_no.size()<4)
        line_no="&nbsp;"+line_no;

      line_no+"&nbsp;&nbsp;";

      tmp += escape_html(line.text);

      if(line.line_number == line_int)
        tmp="<em>"+tmp+"</em>";

      break;
    }

    dest+=tmp+"\n";
  }
}

void document_propertiest::doit()
{
  typedef std::map<source_locationt, doc_claimt> claim_sett;
  claim_sett claim_set;

  forall_goto_functions(f_it, goto_functions)
  {
    const goto_programt &goto_program=f_it->second.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_assert())
      {
        source_locationt new_source_location;

        new_source_location.set_file(i_it->source_location.get_file());
        new_source_location.set_line(i_it->source_location.get_line());
        new_source_location.set_function(i_it->source_location.get_function());

        claim_set[new_source_location].comment_set.
          insert(i_it->source_location.get_comment());
      }
    }
  }

  for(const auto &claim : claim_set)
  {
    std::string code;
    const source_locationt &source_location = claim.first;

    get_code(source_location, code);

    switch(format)
    {
    case LATEX:
      out << "\\claimlocation{File "
          << escape_latex(source_location.get_string("file"), false)
          << " function "
          << escape_latex(source_location.get_string("function"), false)
          << "}\n";

      out << '\n';

      for(const auto &comment : claim.second.comment_set)
        out << "\\claim{" << escape_latex(id2string(comment), false) << "}\n";

      out << '\n';

      out << "\\begin{alltt}\\claimcode\n"
          << code
          << "\\end{alltt}\n";

      out << '\n';
      out << '\n';
      break;

    case HTML:
      out << "<div class=\"claim\">\n"
          << "<div class=\"location\">File "
          << escape_html(source_location.get_string("file"))
          << " function "
          << escape_html(source_location.get_string("function"))
          << "</div>\n";

      out << '\n';

      for(const auto &comment : claim.second.comment_set)
        out << "<div class=\"description\">\n"
            << escape_html(id2string(comment)) << '\n'
            << "</div>\n";

      out << '\n';

      out << "<div class=\"code\">\n"
          << code
          << "</div> <!-- code -->\n";

      out << "</div> <!-- claim -->\n";
      out << '\n';
      break;
    }
  }
}

void document_properties_html(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  document_propertiest(goto_model.goto_functions, out).html();
}

void document_properties_latex(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  document_propertiest(goto_model.goto_functions, out).latex();
}
