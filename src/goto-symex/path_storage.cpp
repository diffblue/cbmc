/*******************************************************************\

Module: Path Storage

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "path_storage.h"

#include <algorithm>
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
// path_dispatch_loopt

path_dispatch_loopt::path_dispatch_loopt(
  const dispatch_loop_detectort &detector,
  messaget &log)
  : dispatch_loop(detector),
    last_peeked(paths.end()),
    log(log),
    last_program_instruction(init_last_program_instruction()),
    case_locations(init_case_locations()),
    targets_cache(init_targets_cache()),
    jump_back_instruction(std::prev(dispatch_loop.subsequent_instruction())),
    look_out_for_cases(false),
    should_adjust_qq(false),
    invalid(init_invalid()),
    old_qq_head(invalid)
{
}

void path_dispatch_loopt::notify_next_instruction(
  const goto_programt::const_targett &instruction,
  goto_symex_statet &state)
{
  if(instruction->location_number == last_program_instruction->location_number)
  {
    log.debug() << "End of path" << log.eom;
    should_adjust_qq = true;
    look_out_for_cases = true;
    return;
  }

  if(instruction->location_number == jump_back_instruction->location_number)
  {
    log.debug() << "Starting path merging at "
                << instruction->source_location.as_string() << log.eom;
    state.doing_path_exploration = false;
    return;
  }

  if(
    instruction->location_number ==
    dispatch_loop.first_instruction()->location_number)
  {
    look_out_for_cases = true;
    return;
  }
  if(!look_out_for_cases)
    return;

  if(case_locations.find(instruction->location_number) == case_locations.end())
    return;

  INVARIANT(
    instruction->has_target(),
    "`instruction' is a case of a dispatch loop, so it should have a target");

  log.debug() << "Starting path exploration at "
              << instruction->source_location.as_string() << log.eom;
  state.doing_path_exploration = true;
  look_out_for_cases = false;
}

path_storaget::patht &path_dispatch_loopt::private_peek()
{
  print_qq("peek");
  const auto front_queue = find_front_queue();
  INVARIANT(
    !front_queue->second.empty(),
    "The queue to peek at should have been set to a non-empty queue by "
    "advance_to_next_path_queue when the end of the dispatch loop was "
    "reached");
  last_peeked = std::prev(front_queue->second.end());
  return front_queue->second.back();
}

void path_dispatch_loopt::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  print_qq("push");
  const goto_programt::const_targett next_pc =
    std::next(next_instruction.state.source.pc);
  const goto_programt::const_targett jump_pc =
    jump_target.state.source.pc->get_target();
  log.debug() << "Looking up in targets cache: <"
              << std::to_string(next_pc->location_number) << " "
              << next_pc->source_location.get_line().c_str() << ", "
              << std::to_string(jump_pc->location_number) << " "
              << jump_pc->source_location.get_line().c_str() << ">" << log.eom;
  const auto &cached_target = std::find_if(
    targets_cache.begin(),
    targets_cache.end(),
    [&next_pc, &jump_pc](
      const std::pair<queue_pointert, goto_programt::const_targett> &qp) {
      return qp.first.originating_branch->location_number ==
               next_pc->location_number &&
             qp.first.branch_target->location_number ==
               jump_pc->location_number;
    });
  if(cached_target == targets_cache.end())
  {
    // The usual case: add both targets to the worklist of the currently-active
    // dispatch case
    INVARIANT(
      !qq.empty(),
      "If we're doing path exploration, the queue queue should already have "
      "had at least two dispatch cases added to it");
    auto front_queue = find_front_queue();
    log.debug() << "Pushing to queue headed by "
                << front_queue->first.to_string() << log.eom;
    front_queue->second.push_back(next_instruction);
    front_queue->second.push_back(jump_target);
    print_qq("after push");
    return;
  }
  // next_instruction and jump_target are the two instructions that a dispatch
  // case leads to. They need to be put in their own queues.
  log.debug() << "Dispersing to two different queues: (["
              << next_pc->location_number << ", "
              << next_pc->source_location.get_line().c_str() << "], ["
              << jump_pc->location_number << ", "
              << jump_pc->source_location.get_line().c_str() << "])" << log.eom;

  const auto &dispatch_case = cached_target->second;
  bool should_swap = false;
  queue_pointert saved = invalid;
  if(!qq.empty())
    saved = qq.front();

  for(const auto &subsequent : {std::make_pair(jump_target, jump_pc),
                                std::make_pair(next_instruction, next_pc)})
  {
    queue_pointert queue_head(dispatch_case, subsequent.second);
    auto found = std::find(qq.begin(), qq.end(), queue_head);
    if(found == qq.end())
    {
      std::list<patht> &queue = queues[queue_head];
      queue.push_back(subsequent.first);
      qq.push_front(queue_head);
    }
    else
    {
      auto front_queue = find_front_queue();
      front_queue->second.push_back(subsequent.first);
      should_swap = true;
    }
  }

  if(should_swap)
    std::iter_swap(std::prev(qq.end()), std::prev(std::prev(qq.end())));

  if(saved != invalid)
  {
    qq.remove(saved);
    qq.push_front(saved);
    should_adjust_qq = true;
  }

  print_qq("after push");
}

void path_dispatch_loopt::private_pop()
{
  PRECONDITION(last_peeked != paths.end());

  INVARIANT(
    !qq.empty(),
    "The queue queue should contain at least the dispatch case that is at "
    "the beginning of the path we were exploring");

  print_qq("pop");

  const auto front_queue = find_front_queue();
  INVARIANT(
    !front_queue->second.empty(),
    "The queue to peek at should have been set to a non-empty queue by "
    "advance_to_next_path_queue when the end of the dispatch loop was "
    "reached");

  front_queue->second.erase(last_peeked);
  last_peeked = paths.end();

  if(should_adjust_qq)
    adjust_queue_queues();

  print_qq("after pop");
}

void path_dispatch_loopt::adjust_queue_queues()
{
  if(empty())
    return;
  log.debug() << "Rejigging" << log.eom;
  should_adjust_qq = false;
  queue_pointert &current_qq_front = qq.front();
  qq.pop_front();
  qq.push_back(current_qq_front);

  auto next_queue_candidate = find_front_queue();

  while(next_queue_candidate->second.empty())
  {
    INVARIANT(
      qq.front() != current_qq_front,
      "There should be a pointer to a non-empty queue in the queue queue, "
      "but we've wrapped all the way around the queue queue looking for one.");
    current_qq_front = qq.front();
    qq.pop_front();
    qq.push_back(current_qq_front);
    next_queue_candidate = find_front_queue();
  }
}

std::size_t path_dispatch_loopt::size() const
{
  std::size_t ret = 0;
  for(const auto &pair : queues)
    ret += pair.second.size();
  return ret;
}

void path_dispatch_loopt::clear()
{
  for(auto &pair : queues)
    while(!pair.second.empty())
      pair.second.pop_back();
}

const std::unordered_set<unsigned>
path_dispatch_loopt::init_case_locations() const
{
  std::unordered_set<unsigned> ret(dispatch_loop.cases().size());
  for(const auto &target : dispatch_loop.cases())
    ret.insert(target->location_number);
  return ret;
}

const goto_programt::const_targett
path_dispatch_loopt::init_last_program_instruction() const
{
  const irep_idt &ep = goto_functionst::entry_point();
  const auto main = dispatch_loop.goto_functions.function_map.find(ep);
  INVARIANT(
    main != dispatch_loop.goto_functions.function_map.end(),
    "There should be an entry point in the goto-functions");
  return main->second.body.get_end_function();
}

const path_dispatch_loopt::queue_pointert
path_dispatch_loopt::init_invalid() const
{
  const irep_idt &ep = goto_functionst::entry_point();
  const auto main = dispatch_loop.goto_functions.function_map.find(ep);
  INVARIANT(
    main != dispatch_loop.goto_functions.function_map.end(),
    "There should be an entry point in the goto-functions");
  return queue_pointert(
    main->second.body.instructions.end(), main->second.body.instructions.end());
}

const std::
  map<path_dispatch_loopt::queue_pointert, goto_programt::const_targett>
  path_dispatch_loopt::init_targets_cache() const
{
  std::map<queue_pointert, goto_programt::const_targett> ret;
  log.debug() << "Targets cache:" << log.eom;
  for(const auto &case_ins : dispatch_loop.cases())
  {
    goto_programt::const_targett next_ins = std::next(case_ins);
    ret[queue_pointert(next_ins, case_ins->get_target())] = case_ins;
    log.debug() << case_ins->location_number << " "
                << case_ins->source_location.as_string() << log.eom;
    log.debug() << "  " << next_ins->location_number << " "
                << "  " << next_ins->source_location.get_line().c_str()
                << log.eom;
    log.debug() << "  " << case_ins->get_target()->location_number << " "
                << "  "
                << case_ins->get_target()->source_location.get_line().c_str()
                << log.eom;
  }
  return ret;
}

void path_dispatch_loopt::print_qq(const std::string &txt) const
{
  log.debug() << txt << " Queues:" << log.eom;

  std::list<std::pair<queue_pointert, std::list<patht>>> sorted;
  for(const auto &pair : queues)
    sorted.push_back(pair);
  sorted.sort([this](
                const std::pair<queue_pointert, std::list<patht>> &item1,
                const std::pair<queue_pointert, std::list<patht>> &item2) {
    const auto pos1 = std::find(qq.begin(), qq.end(), item1.first);
    const auto pos2 = std::find(qq.begin(), qq.end(), item2.first);
    if(pos1 == qq.end())
      return false;
    if(pos2 == qq.end())
      return true;
    const auto idx1 = std::distance(qq.begin(), pos1);
    const auto idx2 = std::distance(qq.begin(), pos2);
    return idx1 < idx2;
  });

  for(const auto &pair : sorted)
  {
    log.debug() << "  " << pair.first.to_string() << " (" << pair.second.size()
                << ")";
    const auto found = std::find(qq.begin(), qq.end(), pair.first);
    if(found == qq.end())
      log.debug() << " *";
    if(pair.first == qq.front())
      log.debug() << " <-";
    log.debug() << log.eom;
  }
}

std::string path_dispatch_loopt::queue_pointert::to_string() const
{
  std::stringstream ss;
  ss << "(" << originating_branch->location_number << "/"
     << originating_branch->source_location.get_file().c_str() << ":"
     << originating_branch->source_location.get_line().c_str() << ", "
     << branch_target->location_number << "/"
     << branch_target->source_location.get_file().c_str() << ":"
     << branch_target->source_location.get_line().c_str() << " "
     << (initialized ? "T" : "F") << ")";
  return ss.str();
}

// _____________________________________________________________________________
// path_strategy_choosert

std::string path_strategy_choosert::show_strategies() const
{
  std::stringstream ss;
  for(auto &pair : strategies)
    ss << pair.second.first;
  return ss.str();
}

void path_strategy_choosert::set_path_strategy_options(
  const cmdlinet &cmdline,
  optionst &options,
  messaget &message) const
{
  if(cmdline.isset("paths"))
  {
    options.set_option("paths", true);
    std::string strategy = cmdline.get_value("paths");
    if(!is_valid_strategy(strategy))
    {
      message.error() << "Unknown strategy '" << strategy
                      << "'. Pass the --show-symex-strategies flag to list "
                         "available strategies."
                      << message.eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
    options.set_option("exploration-strategy", strategy);
  }
  else
    options.set_option("exploration-strategy", default_strategy());
}

path_strategy_choosert::path_strategy_choosert()
  : strategies(
      {{"lifo",
        {" lifo                         next instruction is pushed before\n"
         "                              goto target; paths are popped in\n"
         "                              last-in, first-out order. Explores\n"
         "                              the program tree depth-first.\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const path_storaget::strategy_contextt &ctx) {
           return util_make_unique<path_lifot>();
         }}},
       {"fifo",
        {" fifo                         next instruction is pushed before\n"
         "                              goto target; paths are popped in\n"
         "                              first-in, first-out order. Explores\n"
         "                              the program tree breadth-first.\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const path_storaget::strategy_contextt &ctx) {
           return util_make_unique<path_fifot>();
         }}},
       {"dispatch",
        {" dispatch                     try to detect the program's main\n"
         "                              dispatch loop. Path-merge up to\n"
         "                              that point, then explore each case\n"
         "                              of the dispatch loop depth-first,\n"
         "                              one at a time, doing each case in a\n"
         "                              round-robin fashion.\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const path_storaget::strategy_contextt &ctx)
           -> std::unique_ptr<path_storaget> {
           dispatch_loop_detectort detector(
             ctx.goto_functions, ctx.options, ctx.log);
           if(detector.detect_dispatch_loops())
           {
             ctx.log.warning() << "No dispatch loop detected. Using strategy "
                                  "'lifo' instead."
                               << ctx.log.eom;
             return util_make_unique<path_lifot>();
           }
           return util_make_unique<path_dispatch_loopt>(detector, ctx.log);
         }}}})
{
}
