/*******************************************************************\

Module: Count effective lines of code

Author: Michael Tautschnig

Date: December 2012

\*******************************************************************/

#include <iostream>
#include <unordered_set>

#include <util/prefix.h>
#include <util/file_util.h>

#include "count_eloc.h"

typedef std::unordered_set<irep_idt, irep_id_hash> linest;
typedef std::unordered_map<irep_idt, linest, irep_id_hash> filest;
typedef std::unordered_map<irep_idt, filest, irep_id_hash> working_dirst;

/*******************************************************************\

Function: collect_eloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void collect_eloc(
  const goto_functionst &goto_functions,
  working_dirst &dest)
{
  forall_goto_functions(f_it, goto_functions)
  {
    forall_goto_program_instructions(it, f_it->second.body)
    {
      filest &files=dest[it->source_location.get_working_directory()];
      const irep_idt &file=it->source_location.get_file();

      if(!file.empty() &&
         !it->source_location.is_built_in())
        files[file].insert(it->source_location.get_line());
    }
  }
}

/*******************************************************************\

Function: count_eloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void count_eloc(const goto_functionst &goto_functions)
{
  std::size_t eloc=0;

  working_dirst eloc_map;
  collect_eloc(goto_functions, eloc_map);

  for(const std::pair<irep_idt, filest> &files : eloc_map)
    for(const std::pair<irep_idt, linest> &lines : files.second)
      eloc+=lines.second.size();

  std::cout << "Effective lines of code: " << eloc << '\n';
}

/*******************************************************************\

Function: list_eloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void list_eloc(const goto_functionst &goto_functions)
{
  working_dirst eloc_map;
  collect_eloc(goto_functions, eloc_map);

  for(const std::pair<irep_idt, filest> &files : eloc_map)
    for(const std::pair<irep_idt, linest> &lines : files.second)
    {
      std::string file=id2string(lines.first);
      if(!files.first.empty())
        file=concat_dir_file(id2string(files.first), file);

      for(const irep_idt &line : lines.second)
        std::cout << file << ':' << line << '\n';
    }
}
