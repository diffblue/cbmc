/*******************************************************************\

Module: Record and print code coverage of symbolic execution

Author: Michael Tautschnig

Date: March 2016

\*******************************************************************/

/// \file
/// Record and print code coverage of symbolic execution

#include "symex_coverage.h"

#include <ctime>
#include <chrono>
#include <iostream>
#include <fstream>
#include <sstream>

#include <util/xml.h>
#include <util/string2int.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <langapi/language_util.h>

#include <goto-programs/goto_functions_provider.h>
#include <goto-programs/remove_returns.h>

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
    const irep_idt &function_id,
    const goto_functionst::goto_functiont &goto_function,
    const symex_coveraget::coveraget &coverage);

  const irep_idt &get_file() const
  {
    return file_name;
  }

protected:
  irep_idt file_name;

  struct coverage_conditiont
  {
    coverage_conditiont():
      false_taken(false), true_taken(false)
    {
    }

    bool false_taken;
    bool true_taken;
  };

  struct coverage_linet
  {
    coverage_linet():
      hits(0)
    {
    }

    unsigned hits;
    std::map<goto_programt::const_targett, coverage_conditiont>
      conditions;
  };

  typedef std::map<unsigned, coverage_linet>
    coverage_lines_mapt;

  void compute_coverage_lines(
    const goto_programt &goto_program,
    const irep_idt &file_name,
    const symex_coveraget::coveraget &coverage,
    coverage_lines_mapt &dest);
};

static std::string rate(
  std::size_t covered,
  std::size_t total,
  bool per_cent=false)
{
  std::ostringstream oss;

#if 1
  float fraction;

  if(total==0)
    fraction=1.0;
  else
    fraction=static_cast<float>(covered)/static_cast<float>(total);

  if(per_cent)
    oss << fraction*100.0 << '%';
  else
    oss << fraction;
#else
  oss << covered << " of " << total;
#endif

  return oss.str();
}

static std::string rate_detailed(
  std::size_t covered,
  std::size_t total,
  bool per_cent=false)
{
  std::ostringstream oss;
  oss << rate(covered, total, per_cent)
      << " (" << covered << '/' << total << ')';
  return oss.str();
}

goto_program_coverage_recordt::goto_program_coverage_recordt(
  const namespacet &ns,
  const irep_idt &function_id,
  const goto_functionst::goto_functiont &goto_function,
  const symex_coveraget::coveraget &coverage):
  coverage_recordt("method")
{
  INVARIANT(
    goto_function.body_available(),
    "GOTO coverage records should not be created for stub functions");

  // identify the file name, inlined functions aren't properly
  // accounted for
  goto_programt::const_targett end_function=
    --goto_function.body.instructions.end();
  assert(end_function->is_end_function());
  file_name=end_function->source_location.get_file();
  assert(!file_name.empty());

  // compute the maximum coverage of individual source-code lines
  coverage_lines_mapt coverage_lines_map;
  compute_coverage_lines(
    goto_function.body,
    file_name,
    coverage,
    coverage_lines_map);

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
  xml.set_attribute("name", id2string(function_id));

  code_typet sig_type=
    original_return_type(ns.get_symbol_table(), function_id);
  if(sig_type.is_nil())
    sig_type=goto_function.type;
  xml.set_attribute("signature",
                    from_type(ns, function_id, sig_type));

  xml.set_attribute("line-rate",
                    rate_detailed(lines_covered, lines_total));
  xml.set_attribute("branch-rate",
                    rate(branches_covered, branches_total));

  xmlt &lines=xml.new_element("lines");

  for(const auto &cov_line : coverage_lines_map)
  {
    xmlt &line=lines.new_element("line");

    line.set_attribute("number", std::to_string(cov_line.first));
    line.set_attribute("hits", std::to_string(cov_line.second.hits));
    if(cov_line.second.conditions.empty())
      line.set_attribute("branch", "false");
    else
    {
      line.set_attribute("branch", "true");

      xmlt &conditions=line.new_element("conditions");

      std::size_t number=0, total_taken=0;
      for(const auto &c : cov_line.second.conditions)
      {
        // <condition number="0" type="jump" coverage="50%"/>
        xmlt &condition=conditions.new_element("condition");
        condition.set_attribute("number", std::to_string(number++));
        condition.set_attribute("type", "jump");
        unsigned taken=c.second.false_taken+c.second.true_taken;
        total_taken+=taken;
        condition.set_attribute("coverage", rate(taken, 2, true));
      }

      line.set_attribute(
        "condition-coverage",
        rate_detailed(total_taken, number*2, true));
    }
  }
}

void goto_program_coverage_recordt::compute_coverage_lines(
    const goto_programt &goto_program,
    const irep_idt &file_name,
    const symex_coveraget::coveraget &coverage,
    coverage_lines_mapt &dest)
{
  forall_goto_program_instructions(it, goto_program)
  {
    if(it->source_location.is_nil() ||
       it->source_location.get_file()!=file_name ||
       it->is_dead() ||
       it->is_end_function())
      continue;

    const bool is_branch=it->is_goto() && !it->guard.is_constant();

    unsigned l=
      safe_string2unsigned(id2string(it->source_location.get_line()));
    std::pair<coverage_lines_mapt::iterator, bool> entry=
      dest.insert(std::make_pair(l, coverage_linet()));

    if(entry.second)
      ++lines_total;

    // mark as branch if any instruction in this source code line is
    // a branching instruction
    if(is_branch)
    {
      branches_total+=2;
      if(!entry.first->second.conditions.insert(
          {it, coverage_conditiont()}).second)
        UNREACHABLE;
    }

    symex_coveraget::coveraget::const_iterator c_entry=
      coverage.find(it);
    if(c_entry!=coverage.end())
    {
      if(!(c_entry->second.size()==1 || is_branch))
      {
        std::cerr << it->location_number << '\n';
        for(const auto &cov : c_entry->second)
          std::cerr << cov.second.succ->location_number << '\n';
      }
      assert(c_entry->second.size()==1 || is_branch);

      for(const auto &cov : c_entry->second)
      {
        assert(cov.second.num_executions>0);

        if(entry.first->second.hits==0)
          ++lines_covered;

        if(cov.second.num_executions>entry.first->second.hits)
          entry.first->second.hits=cov.second.num_executions;

        if(is_branch)
        {
          auto cond_entry=entry.first->second.conditions.find(it);
          assert(cond_entry!=entry.first->second.conditions.end());

          if(it->get_target()==cov.second.succ)
          {
            if(!cond_entry->second.false_taken)
            {
              cond_entry->second.false_taken=true;
              ++branches_covered;
            }
          }
          else
          {
            if(!cond_entry->second.true_taken)
            {
              cond_entry->second.true_taken=true;
              ++branches_covered;
            }
          }
        }
      }
    }
  }
}

void symex_coveraget::compute_overall_coverage(
  const goto_functions_providert &goto_functions_provider,
  coverage_recordt &dest) const
{
  typedef std::map<irep_idt, coverage_recordt> file_recordst;
  file_recordst file_records;

  for(const irep_idt &function_id :
        goto_functions_provider.get_available_functions())
  {
    const goto_functionst::goto_functiont &goto_function =
      goto_functions_provider.get_existing_goto_function(function_id);
    if(!goto_function.body_available() ||
       function_id==goto_functionst::entry_point() ||
       function_id==CPROVER_PREFIX "initialize")
      continue;

    goto_program_coverage_recordt func_cov(
      ns, function_id, goto_function, coverage);

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

void symex_coveraget::build_cobertura(
  const goto_functions_providert &goto_functions_provider,
  xmlt &xml_coverage) const
{
  coverage_recordt overall_cov("package");
  compute_overall_coverage(goto_functions_provider, overall_cov);

  std::string overall_line_rate_str=
    rate(overall_cov.lines_covered, overall_cov.lines_total);
  std::string overall_branch_rate_str=
    rate(overall_cov.branches_covered, overall_cov.branches_total);

  auto now = std::chrono::system_clock::now();
  auto current_time = std::chrono::time_point_cast<std::chrono::seconds>(now);
  std::time_t tt = std::chrono::system_clock::to_time_t(current_time);

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
                             std::to_string(tt));

  xmlt &packages=xml_coverage.new_element("packages");

  // <package name="" line-rate="0.0" branch-rate="0.0" complexity="0.0">
  xmlt &package=packages.new_element(overall_cov.xml);
  package.set_attribute("name", "");
  package.set_attribute("line-rate", overall_line_rate_str);
  package.set_attribute("branch-rate", overall_branch_rate_str);
  package.set_attribute("complexity", "0.0");
}

bool symex_coveraget::output_report(
  const goto_functions_providert &goto_functions_provider,
  std::ostream &os) const
{
  xmlt xml_coverage("coverage");
  build_cobertura(goto_functions_provider, xml_coverage);

  os << "<?xml version=\"1.0\"?>\n";
  os << "<!DOCTYPE coverage SYSTEM \""
     << "http://cobertura.sourceforge.net/xml/coverage-04.dtd\">\n";
  os << xml_coverage;

  return !os.good();
}

bool symex_coveraget::generate_report(
  const goto_functions_providert &goto_functions_provider,
  const std::string &path) const
{
  assert(!path.empty());

  if(path=="-")
    return output_report(goto_functions_provider, std::cout);
  else
  {
    std::ofstream out(path.c_str());
    return output_report(goto_functions_provider, out);
  }
}
