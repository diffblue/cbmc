/*******************************************************************\

Module: Record and print code coverage of symbolic execution

Author: Michael Tautschnig

Date: March 2016

\*******************************************************************/

#include <iostream>
#include <fstream>
#include <sstream>

#include <util/time_stopping.h>
#include <util/xml.h>
#include <util/string2int.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <goto-programs/goto_functions.h>

#include "symex_coverage.h"

class coverage_recordt
{
public:
  explicit coverage_recordt(const std::string &node_id):
    xml(node_id),
    lines_covered(0),
    lines_total(0),
    branches_covered(0),
    branches_total(0)
  {
  }

  xmlt xml;
  std::size_t lines_covered;
  std::size_t lines_total;
  std::size_t branches_covered;
  std::size_t branches_total;
};

class goto_program_coverage_recordt:public coverage_recordt
{
public:
  goto_program_coverage_recordt(
    const namespacet &ns,
    goto_functionst::function_mapt::const_iterator gf_it,
    const symex_coveraget::coveraget &coverage);

  const irep_idt &get_file() const
  {
    return file_name;
  }

protected:
  irep_idt file_name;

  struct line_coverage_recordt
  {
    line_coverage_recordt():
      hits(0), is_branch(false), branch_covered(false)
    {
    }

    unsigned hits;
    bool is_branch;
    bool branch_covered;
  };

  typedef std::map<unsigned, line_coverage_recordt>
    line_coverage_mapt;

  void compute_line_coverage(
    const goto_programt &goto_program,
    const irep_idt &file_name,
    const symex_coveraget::coveraget &coverage,
    line_coverage_mapt &dest);
};

/*******************************************************************\

Function: rate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::string rate(std::size_t covered, std::size_t total)
{
#if 1
  if(total==0)
    return "1.0";

  std::ostringstream oss;

  oss << static_cast<float>(covered)/static_cast<float>(total);
#else
  std::ostringstream oss;
  oss << covered << " of " << total;
#endif

  return oss.str();
}

/*******************************************************************\

Function: goto_program_coverage_recordt::goto_program_coverage_recordt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_program_coverage_recordt::goto_program_coverage_recordt(
  const namespacet &ns,
  goto_functionst::function_mapt::const_iterator gf_it,
  const symex_coveraget::coveraget &coverage):
  coverage_recordt("method")
{
  assert(gf_it->second.body_available());

  // identify the file name, inlined functions aren't properly
  // accounted for
  goto_programt::const_targett end_function=
    --gf_it->second.body.instructions.end();
  assert(end_function->is_end_function());
  file_name=end_function->source_location.get_file();
  assert(!file_name.empty());

  // compute the maximum coverage of individual source-code lines
  line_coverage_mapt line_coverage_map;
  compute_line_coverage(
    gf_it->second.body,
    file_name,
    coverage,
    line_coverage_map);

  // <method name="foo" signature="int(int)" line-rate="1.0" branch-rate="1.0">
  //   <lines>
  //     <line number="23" hits="1" branch="false"/>
  //     <line number="24" hits="1" branch="false"/>
  //     <line number="25" hits="1" branch="false"/>
  //     <line number="26" hits="1" branch="false"/>
  //     <line number="27" hits="1" branch="false"/>
  //     <line number="28" hits="1" branch="false"/>
  //     <line number="29" hits="1" branch="false"/>
  //     <line number="30" hits="1" branch="false"/>
  //   </lines>
  // </method>
  xml.set_attribute("name", id2string(gf_it->first));
  xml.set_attribute("signature",
                    from_type(ns, gf_it->first, gf_it->second.type));
  xml.set_attribute("line-rate",
                    rate(lines_covered, lines_total));
  xml.set_attribute("branch-rate",
                    rate(branches_covered, branches_total));

  xmlt &lines=xml.new_element("lines");

  for(line_coverage_mapt::const_iterator
      it=line_coverage_map.begin();
      it!=line_coverage_map.end();
      ++it)
  {
    xmlt &line=lines.new_element("line");

    line.set_attribute("number", std::to_string(it->first));
    line.set_attribute("hits", std::to_string(it->second.hits));
    if(!it->second.is_branch)
      line.set_attribute("branch", "false");
    else
    {
      // TODO: conditions
      line.set_attribute("branch", "true");
    }
  }
}

/*******************************************************************\

Function: goto_program_coverage_recordt::compute_line_coverage

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_coverage_recordt::compute_line_coverage(
    const goto_programt &goto_program,
    const irep_idt &file_name,
    const symex_coveraget::coveraget &coverage,
    line_coverage_mapt &dest)
{
  forall_goto_program_instructions(it, goto_program)
  {
    if(it->source_location.is_nil() ||
       it->source_location.get_file()!=file_name)
      continue;

    const bool is_branch=it->is_goto() && !it->guard.is_constant();

    unsigned l=
      safe_string2unsigned(id2string(it->source_location.get_line()));
    std::pair<line_coverage_mapt::iterator, bool> entry=
      dest.insert(std::make_pair(l, line_coverage_recordt()));

    if(entry.second)
    {
      ++lines_total;
      if(is_branch)
        ++branches_total;
    }

    // mark as branch if any instruction in this source code line is
    // a branching instruction
    if(is_branch &&
       !entry.first->second.is_branch)
    {
      ++branches_total;
      entry.first->second.is_branch=true;
    }

    symex_coveraget::coveraget::const_iterator c_entry=
      coverage.find(it);
    if(c_entry!=coverage.end() &&
       c_entry->second.num_executions>0)
    {
      // maximum over all instructions in this source code line
      if(c_entry->second.num_executions>entry.first->second.hits)
      {
        if(entry.first->second.hits==0)
          ++lines_covered;
        entry.first->second.hits=c_entry->second.num_executions;
      }

      if(is_branch && !entry.first->second.branch_covered)
      {
        ++branches_covered;
        entry.first->second.branch_covered=true;
      }
    }
  }
}

/*******************************************************************\

Function: symex_coveraget::compute_overall_coverage

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_coveraget::compute_overall_coverage(
  const goto_functionst &goto_functions,
  coverage_recordt &dest) const
{
  typedef std::map<irep_idt, coverage_recordt> file_recordst;
  file_recordst file_records;

  forall_goto_functions(gf_it, goto_functions)
  {
    if(!gf_it->second.body_available() ||
       gf_it->first==goto_functions.entry_point() ||
       gf_it->first==CPROVER_PREFIX "initialize")
      continue;

    goto_program_coverage_recordt func_cov(ns, gf_it, coverage);

    std::pair<file_recordst::iterator, bool> entry=
      file_records.insert(std::make_pair(func_cov.get_file(),
                                         coverage_recordt("class")));
    coverage_recordt &file_record=entry.first->second;

    if(entry.second)
    {
      file_record.xml.new_element("methods");
      file_record.xml.new_element("lines");
    }

    // copy the "method" node
    file_record.xml.elements.front().new_element(func_cov.xml);

    // copy any lines
    for(xmlt::elementst::const_iterator
        it=func_cov.xml.elements.front().elements.begin();
        it!=func_cov.xml.elements.front().elements.end();
        ++it)
      file_record.xml.elements.back().new_element(*it);

    // merge line/branch info
    file_record.lines_covered+=func_cov.lines_covered;
    file_record.lines_total+=func_cov.lines_total;
    file_record.branches_covered+=func_cov.branches_covered;
    file_record.branches_total+=func_cov.branches_total;
  }

  xmlt &classes=dest.xml.new_element("classes");

  // <class name="MyProject.GameRules" filename="MyProject/GameRules.java"
  //        line-rate="1.0" branch-rate="1.0" complexity="1.4">
  for(file_recordst::const_iterator it=file_records.begin();
      it!=file_records.end();
      ++it)
  {
    if(source_locationt::is_built_in(id2string(it->first)))
      continue;

    const coverage_recordt &f_cov=it->second;

    xmlt &class_xml=classes.new_element(f_cov.xml);
    class_xml.set_attribute("name", id2string(it->first));
    class_xml.set_attribute("filename", id2string(it->first));
    class_xml.set_attribute("line-rate",
                            rate(f_cov.lines_covered,
                                 f_cov.lines_total));
    class_xml.set_attribute("branch-rate",
                            rate(f_cov.branches_covered,
                                 f_cov.branches_total));
    class_xml.set_attribute("complexity", "0.0");

    // merge line/branch info
    dest.lines_covered+=f_cov.lines_covered;
    dest.lines_total+=f_cov.lines_total;
    dest.branches_covered+=f_cov.branches_covered;
    dest.branches_total+=f_cov.branches_total;
  }
}

/*******************************************************************\

Function: symex_coveraget::build_cobertura

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_coveraget::build_cobertura(
  const goto_functionst &goto_functions,
  xmlt &xml_coverage) const
{
  coverage_recordt overall_cov("package");
  compute_overall_coverage(goto_functions, overall_cov);

  std::string overall_line_rate_str=
    rate(overall_cov.lines_covered, overall_cov.lines_total);
  std::string overall_branch_rate_str=
    rate(overall_cov.branches_covered, overall_cov.branches_total);

  // <coverage line-rate="0.0" branch-rate="0.0" lines-covered="1"
  //           lines-valid="1" branches-covered="1"
  //           branches-valid="1" complexity="0.0"
  //           version="2.1.1" timestamp="0">
  xml_coverage.set_attribute("line-rate", overall_line_rate_str);
  xml_coverage.set_attribute("branch-rate", overall_branch_rate_str);
  xml_coverage.set_attribute("lines-covered",
                             std::to_string(overall_cov.lines_covered));
  xml_coverage.set_attribute("lines-valid",
                             std::to_string(overall_cov.lines_total));
  xml_coverage.set_attribute("branches-covered",
                             std::to_string(overall_cov.branches_covered));
  xml_coverage.set_attribute("branches-valid",
                             std::to_string(overall_cov.branches_total));
  xml_coverage.set_attribute("complexity", "0.0");
  xml_coverage.set_attribute("version", "2.1.1");
  xml_coverage.set_attribute("timestamp",
                             std::to_string(current_time().get_t()));

  xmlt &packages=xml_coverage.new_element("packages");

  // <package name="" line-rate="0.0" branch-rate="0.0" complexity="0.0">
  xmlt &package=packages.new_element(overall_cov.xml);
  package.set_attribute("name", "");
  package.set_attribute("line-rate", overall_line_rate_str);
  package.set_attribute("branch-rate", overall_branch_rate_str);
  package.set_attribute("complexity", "0.0");
}

/*******************************************************************\

Function: symex_coveraget::output_report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_coveraget::output_report(
  const goto_functionst &goto_functions,
  std::ostream &os) const
{
  xmlt xml_coverage("coverage");
  build_cobertura(goto_functions, xml_coverage);

  os << "<?xml version=\"1.0\"?>\n";
  os << "<!DOCTYPE coverage SYSTEM \""
     << "http://cobertura.sourceforge.net/xml/coverage-04.dtd\">\n";
  os << xml_coverage;

  return !os.good();
}

/*******************************************************************\

Function: symex_coveraget::output_report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_coveraget::generate_report(
  const goto_functionst &goto_functions,
  const std::string &path) const
{
  assert(!path.empty());

  if(path=="-")
    return output_report(goto_functions, std::cout);
  else
  {
    std::ofstream out(path.c_str());
    return output_report(goto_functions, out);
  }
}

