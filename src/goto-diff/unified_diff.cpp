/*******************************************************************\

Module: Unified diff (using LCSS) of goto functions

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// Unified diff (using LCSS) of goto functions

#include "unified_diff.h"

#include <algorithm>

#include <goto-programs/goto_model.h>

unified_difft::unified_difft(const goto_modelt &model_old,
                             const goto_modelt &model_new):
  old_goto_functions(model_old.goto_functions),
  ns_old(model_old.symbol_table),
  new_goto_functions(model_new.goto_functions),
  ns_new(model_new.symbol_table)
{
}

void unified_difft::get_diff(
  const irep_idt &function,
  goto_program_difft &dest) const
{
  dest.clear();

  differences_mapt::const_iterator entry=
    differences_map.find(function);
  if(entry==differences_map.end())
    return;

  goto_functionst::function_mapt::const_iterator old_fit=
    old_goto_functions.function_map.find(function);
  goto_functionst::function_mapt::const_iterator new_fit=
    new_goto_functions.function_map.find(function);

  goto_programt empty;

  const goto_programt &old_goto_program=
    old_fit==old_goto_functions.function_map.end() ?
    empty :
    old_fit->second.body;
  const goto_programt &new_goto_program=
    new_fit==new_goto_functions.function_map.end() ?
    empty :
    new_fit->second.body;

  get_diff(
    function,
    old_goto_program,
    new_goto_program,
    entry->second,
    dest);
}

void unified_difft::get_diff(
  const irep_idt &identifier,
  const goto_programt &old_goto_program,
  const goto_programt &new_goto_program,
  const differencest &differences,
  goto_program_difft &dest) const
{
  goto_programt::instructionst::const_iterator old_it=
    old_goto_program.instructions.begin();
  goto_programt::instructionst::const_iterator new_it=
    new_goto_program.instructions.begin();

  for(differencest::const_reverse_iterator rit=differences.rbegin();
      rit!=differences.rend();
      ++rit)
  {
    switch(*rit)
    {
      case differencet::SAME:
        dest.push_back(std::make_pair(new_it, differencet::SAME));
        assert(old_it!=old_goto_program.instructions.end());
        ++old_it;
        assert(new_it!=new_goto_program.instructions.end());
        ++new_it;
        break;
      case differencet::DELETED:
        dest.push_back(std::make_pair(old_it, differencet::DELETED));
        assert(old_it!=old_goto_program.instructions.end());
        ++old_it;
        break;
      case differencet::NEW:
        dest.push_back(std::make_pair(new_it, differencet::NEW));
        assert(new_it!=new_goto_program.instructions.end());
        ++new_it;
        break;
    }
  }
}

void unified_difft::output_diff(
  const irep_idt &identifier,
  const goto_programt &old_goto_program,
  const goto_programt &new_goto_program,
  const differencest &differences,
  std::ostream &os) const
{
  goto_program_difft diff;
  get_diff(
    identifier,
    old_goto_program,
    new_goto_program,
    differences,
    diff);

  bool has_diff=false;
  for(const auto &d : diff)
  {
    if(d.second!=differencet::SAME)
    {
      has_diff=true;
      break;
    }
  }
  if(!has_diff)
    return;

  os << "/** " << identifier << " **/\n";

  for(const auto &d : diff)
  {
    switch(d.second)
    {
      case differencet::SAME:
        os << ' ';
        new_goto_program.output_instruction(
          ns_new,
          identifier,
          os,
          d.first);
        break;
      case differencet::DELETED:
        os << '-';
        old_goto_program.output_instruction(
          ns_old,
          identifier,
          os,
          d.first);
        break;
      case differencet::NEW:
        os << '+';
        new_goto_program.output_instruction(
          ns_new,
          identifier,
          os,
          d.first);
        break;
    }
  }
}

void unified_difft::lcss(
  const irep_idt &identifier,
  const goto_programt &old_goto_program,
  const goto_programt &new_goto_program,
  differencest &differences) const
{
  std::size_t old_count=old_goto_program.instructions.size();
  std::size_t new_count=new_goto_program.instructions.size();

  differences.reserve(old_count+new_count);

  // skip common prefix
  goto_programt::instructionst::const_iterator old_it=
    old_goto_program.instructions.begin();
  goto_programt::instructionst::const_iterator new_it=
    new_goto_program.instructions.begin();

  for( ;
       old_it!=old_goto_program.instructions.end() &&
       new_it!=new_goto_program.instructions.end();
       ++old_it, ++new_it)
  {
    if(!instructions_equal(*old_it, *new_it))
      break;

    --old_count;
    --new_count;
  }
  // old_it, new_it are now iterators to the first instructions that
  // differ

  // skip common suffix
  goto_programt::instructionst::const_iterator old_rit=
    old_goto_program.instructions.end();
  goto_programt::instructionst::const_iterator new_rit=
    new_goto_program.instructions.end();

  while(old_rit!=old_it && new_rit!=new_it)
  {
    --old_rit;
    --new_rit;

    if(!instructions_equal(*old_rit, *new_rit))
    {
      ++old_rit;
      ++new_rit;
      break;
    }

    --old_count;
    --new_count;
    differences.push_back(differencet::SAME);
  }
  // old_rit, new_rit are now iterators to the first instructions of
  // the common tail

  if(old_count==0 && new_count==0)
    return;

  // apply longest common subsequence (LCSS)
  using lcss_matrixt = std::vector<std::vector<std::size_t> >;
  lcss_matrixt lcss_matrix(
    old_count+1,
    std::vector<size_t>(new_count+1, 0));

  // fill the matrix
  std::size_t i=1, j=1;
  for(goto_programt::instructionst::const_iterator old_it2=old_it;
      old_it2!=old_rit;
      ++old_it2)
  {
    j=1;
    for(goto_programt::instructionst::const_iterator new_it2=new_it;
        new_it2!=new_rit;
        ++new_it2)
    {
      if(instructions_equal(*old_it2, *new_it2))
        lcss_matrix[i][j]+=lcss_matrix[i-1][j-1]+1;
      else
        lcss_matrix[i][j]=
          std::max(lcss_matrix[i][j-1], lcss_matrix[i-1][j]);

      ++j;
    }
    ++i;
  }

  #if 0
  std::cerr << "old_count=" << old_count << '\n';
  std::cerr << "new_count=" << new_count << '\n';
  for(i=0; i<=old_count; ++i)
  {
    for(j=0; j<=new_count; ++j)
    {
      std::cerr << " ";
      if(lcss_matrix[i][j]<10)
        std::cerr << " ";
      std::cerr << lcss_matrix[i][j];
    }
    std::cerr << '\n';
  }
  #endif

  // backtracking
  // note that the order in case of multiple possible matches of
  // the if-clauses is important to provide a convenient ordering
  // of - and + lines (- goes before +)
  i=old_count;
  j=new_count;
  --old_rit;
  --new_rit;

  while(i>0 || j>0)
  {
    if(i==0)
    {
      differences.push_back(differencet::NEW);
      --j;
      --new_rit;
    }
    else if(j==0)
    {
      differences.push_back(differencet::DELETED);
      --i;
      --old_rit;
    }
    else if(instructions_equal(*old_rit, *new_rit))
    {
      differences.push_back(differencet::SAME);
      --i;
      --old_rit;
      --j;
      --new_rit;
    }
    else if(lcss_matrix[i][j-1]<lcss_matrix[i][j])
    {
      differences.push_back(differencet::DELETED);
      --i;
      --old_rit;
    }
    else
    {
      differences.push_back(differencet::NEW);
      --j;
      --new_rit;
    }
  }

  // add common prefix (if any)
  for( ; old_it!=old_goto_program.instructions.begin(); --old_it)
    differences.push_back(differencet::SAME);
}

void unified_difft::unified_diff(
  const irep_idt &identifier,
  const goto_programt &old_goto_program,
  const goto_programt &new_goto_program)
{
  differencest &differences=differences_map[identifier];
  differences.clear();

  if(old_goto_program.instructions.empty() ||
     new_goto_program.instructions.empty())
  {
    if(new_goto_program.instructions.empty())
      differences.resize(
        old_goto_program.instructions.size(),
        differencet::DELETED);
    else
      differences.resize(
        new_goto_program.instructions.size(),
        differencet::NEW);
  }
  else
    lcss(identifier, old_goto_program, new_goto_program, differences);
}

bool unified_difft::operator()()
{
  using function_mapt =
    std::map<irep_idt, goto_functionst::function_mapt::const_iterator>;

  function_mapt old_funcs, new_funcs;

  forall_goto_functions(it, old_goto_functions)
    old_funcs.insert(std::make_pair(it->first, it));
  forall_goto_functions(it, new_goto_functions)
    new_funcs.insert(std::make_pair(it->first, it));

  goto_programt empty;

  function_mapt::const_iterator ito=old_funcs.begin();
  for(function_mapt::const_iterator itn=new_funcs.begin();
      itn!=new_funcs.end();
      ++itn)
  {
    for( ;
        ito!=old_funcs.end() && ito->first<itn->first;
        ++ito)
      unified_diff(ito->first, ito->second->second.body, empty);

    if(ito==old_funcs.end() || itn->first<ito->first)
      unified_diff(itn->first, empty, itn->second->second.body);
    else
    {
      assert(ito->first==itn->first);
      unified_diff(
        itn->first,
        ito->second->second.body,
        itn->second->second.body);
      ++ito;
    }
  }
  for( ; ito!=old_funcs.end(); ++ito)
    unified_diff(ito->first, ito->second->second.body, empty);

  return !differences_map.empty();
}

void unified_difft::output(std::ostream &os) const
{
  goto_programt empty;

  for(const std::pair<irep_idt, differencest> &p : differences_map)
  {
    goto_functionst::function_mapt::const_iterator f1=
      old_goto_functions.function_map.find(p.first);
    goto_functionst::function_mapt::const_iterator f2=
      new_goto_functions.function_map.find(p.first);

    output_diff(
      p.first,
      f1==old_goto_functions.function_map.end()?empty:f1->second.body,
      f2==new_goto_functions.function_map.end()?empty:f2->second.body,
      p.second,
      os);
  }
}
