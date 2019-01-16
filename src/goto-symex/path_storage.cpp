/*******************************************************************\

Module: Path Storage

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "path_storage.h"

#include <sstream>

#include <util/exit_codes.h>
#include <util/make_unique.h>

// _____________________________________________________________________________
// path_lifot

path_storaget::patht &path_lifot::private_peek()
{
  last_peeked = paths.end();
  --last_peeked;
  return paths.back();
}

void path_lifot::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  paths.push_back(next_instruction);
  paths.push_back(jump_target);
}

void path_lifot::private_pop()
{
  PRECONDITION(last_peeked != paths.end());
  paths.erase(last_peeked);
  last_peeked = paths.end();
}

std::size_t path_lifot::size() const
{
  return paths.size();
}

void path_lifot::clear()
{
  paths.clear();
}

// _____________________________________________________________________________
// path_fifot

path_storaget::patht &path_fifot::private_peek()
{
  return paths.front();
}

void path_fifot::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  paths.push_back(next_instruction);
  paths.push_back(jump_target);
}

void path_fifot::private_pop()
{
  paths.pop_front();
}

std::size_t path_fifot::size() const
{
  return paths.size();
}

void path_fifot::clear()
{
  paths.clear();
}

// _____________________________________________________________________________
// path_strategy_choosert

static const std::map<
  const std::string,
  std::pair<
    const std::string,
    const std::function<std::unique_ptr<path_storaget>()>>>
  path_strategies(
    {{"lifo",
      {" lifo                         next instruction is pushed before\n"
       "                              goto target; paths are popped in\n"
       "                              last-in, first-out order. Explores\n"
       "                              the program tree depth-first.\n",
       []() { // NOLINT(whitespace/braces)
         return util_make_unique<path_lifot>();
       }}},
     {"fifo",
      {" fifo                         next instruction is pushed before\n"
       "                              goto target; paths are popped in\n"
       "                              first-in, first-out order. Explores\n"
       "                              the program tree breadth-first.\n",
       []() { // NOLINT(whitespace/braces)
         return util_make_unique<path_fifot>();
       }}}});

std::string show_path_strategies()
{
  std::stringstream ss;
  for(auto &pair : path_strategies)
    ss << pair.second.first;
  return ss.str();
}

std::string default_path_strategy()
{
  return "lifo";
}

bool is_valid_path_strategy(const std::string strategy)
{
  return path_strategies.find(strategy) != path_strategies.end();
}

std::unique_ptr<path_storaget> get_path_strategy(const std::string strategy)
{
  auto found = path_strategies.find(strategy);
  INVARIANT(
    found != path_strategies.end(), "Unknown strategy '" + strategy + "'.");
  return found->second.second();
}

void parse_path_strategy_options(
  const cmdlinet &cmdline,
  optionst &options,
  message_handlert &message_handler)
{
  messaget log(message_handler);
  if(cmdline.isset("paths"))
  {
    options.set_option("paths", true);
    std::string strategy = cmdline.get_value("paths");
    if(!is_valid_path_strategy(strategy))
    {
      log.error() << "Unknown strategy '" << strategy
                  << "'. Pass the --show-symex-strategies flag to list "
                     "available strategies."
                  << messaget::eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
    options.set_option("exploration-strategy", strategy);
  }
  else
  {
    options.set_option("exploration-strategy", default_path_strategy());
  }
}
