/*******************************************************************\

Module: goto-analyzer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "show_on_source.h"

#include <util/file_util.h>
#include <util/message.h>
#include <util/unicode.h>

#include <analyses/ai.h>

#include <fstream>

/// get the name of the file referred to at a location loc,
/// if any
static optionalt<std::string>
show_location(const ai_baset &ai, ai_baset::locationt loc)
{
  const auto abstract_state = ai.abstract_state_before(loc);
  if(abstract_state->is_top())
    return {};

  if(loc->source_location.get_line().empty())
    return {};

  return loc->source_location.full_path();
}

/// get the source files with non-top abstract states
static std::set<std::string>
get_source_files(const goto_modelt &goto_model, const ai_baset &ai)
{
  std::set<std::string> files;

  for(const auto &f : goto_model.goto_functions.function_map)
  {
    forall_goto_program_instructions(i_it, f.second.body)
    {
      const auto file = show_location(ai, i_it);
      if(file.has_value())
        files.insert(file.value());
    }
  }

  return files;
}

/// print a string with indent to match given sample line
static void print_with_indent(
  const std::string &src,
  const std::string &indent_line,
  std::ostream &out)
{
  const std::size_t p = indent_line.find_first_not_of(" \t");
  const std::string indent =
    p == std::string::npos ? std::string("") : std::string(indent_line, 0, p);
  std::istringstream in(src);
  std::string src_line;
  while(std::getline(in, src_line))
    out << indent << src_line << '\n';
}

/// output source code annotated with abstract states for given file
void show_on_source(
  const std::string &source_file,
  const goto_modelt &goto_model,
  const ai_baset &ai,
  message_handlert &message_handler)
{
#ifdef _MSC_VER
  std::ifstream in(widen(source_file));
#else
  std::ifstream in(source_file);
#endif

  messaget message(message_handler);

  if(!in)
  {
    message.warning() << "Failed to open `" << source_file << "'"
                      << messaget::eom;
    return;
  }

  std::map<std::size_t, ai_baset::locationt> line_map;

  // Collect line numbers with non-top abstract states.
  // We pick the _first_ state for each line.
  for(const auto &f : goto_model.goto_functions.function_map)
  {
    forall_goto_program_instructions(i_it, f.second.body)
    {
      const auto file = show_location(ai, i_it);
      if(file.has_value() && file.value() == source_file)
      {
        const std::size_t line_no =
          stoull(id2string(i_it->source_location.get_line()));
        if(line_map.find(line_no) == line_map.end())
          line_map[line_no] = i_it;
      }
    }
  }

  // now print file to message handler
  const namespacet ns(goto_model.symbol_table);

  std::string line;
  for(std::size_t line_no = 1; std::getline(in, line); line_no++)
  {
    const auto map_it = line_map.find(line_no);
    if(map_it != line_map.end())
    {
      auto abstract_state = ai.abstract_state_before(map_it->second);
      std::ostringstream state_str;
      abstract_state->output(state_str, ai, ns);
      if(!state_str.str().empty())
      {
        message.result() << messaget::blue;
        print_with_indent(state_str.str(), line, message.result());
        message.result() << messaget::reset;
      }
    }

    message.result() << line << messaget::eom;
  }
}

/// output source code annotated with abstract states
void show_on_source(
  const goto_modelt &goto_model,
  const ai_baset &ai,
  message_handlert &message_handler)
{
  // first gather the source files that have something to show
  const auto source_files = get_source_files(goto_model, ai);

  // now show file-by-file
  for(const auto &source_file : source_files)
    show_on_source(source_file, goto_model, ai, message_handler);
}
