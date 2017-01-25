/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <iterator>

#ifndef _WIN32
#include <cstdlib>
#include <sys/wait.h>
#include <unistd.h>
#endif

#include <cegis/symex/cegis_symex_verify.h>

#include <cegis/danger/symex/verify/restrict_counterexamples.h>
#include <cegis/danger/symex/verify/parallel_danger_verify_task.h>

parallel_danger_verify_taskt::parallel_danger_verify_taskt(
    const optionst &options, danger_verify_configt &config,
    const candidatet &candidate, modet mode) :
    options(options), config(config), candidate(candidate), mode(mode), success(
        false), child_pid(-1)
{
}

parallel_danger_verify_taskt::~parallel_danger_verify_taskt()
{
}

parallel_danger_verify_taskt::parallel_danger_verify_taskt(
    const parallel_danger_verify_taskt &other) :
    options(other.options), config(other.config), candidate(other.candidate), mode(
        other.mode), success(other.success), pipe(other.pipe), child_pid(other.child_pid)
{
  pipe.auto_close();
}

void parallel_danger_verify_taskt::set_parent_mode(const pid_t child_pid)
{
  pipe.close_write();
  this->child_pid=child_pid;
}

pid_t parallel_danger_verify_taskt::get_child_pid() const
{
  return child_pid;
}

namespace
{
class danger_config_fullt
{
  danger_verify_configt &config;
public:
  typedef danger_verify_configt::counterexamplet counterexamplet;
  typedef danger_verify_configt::counterexamplest counterexamplest;
  typedef danger_verify_configt::candidatet candidatet;

  danger_config_fullt(danger_verify_configt &config) :
      config(config)
  {
  }

  void process(const candidatet &candidate)
  {
    // Already pre-processed
  }

  const symbol_tablet &get_symbol_table()
  {
    return config.get_symbol_table();
  }

  const goto_functionst &get_goto_functions()
  {
    return config.get_goto_functions();
  }

  void convert(counterexamplest &counterexamples, const goto_tracet &trace)
  {
    config.convert(counterexamples, trace);
  }
};

class danger_config_rankingt
{
  danger_verify_configt &config;
  goto_functionst &gf;
public:
  typedef danger_verify_configt::counterexamplet counterexamplet;
  typedef danger_verify_configt::counterexamplest counterexamplest;
  typedef danger_verify_configt::candidatet candidatet;

  danger_config_rankingt(danger_verify_configt &config) :
      config(config), gf(config.get_goto_functions())
  {
  }

  void process(const candidatet &candidate)
  {
    force_ranking_error(gf, config.get_number_of_loops());
  }

  const symbol_tablet &get_symbol_table()
  {
    return config.get_symbol_table();
  }

  const goto_functionst &get_goto_functions()
  {
    return gf;
  }

  void convert(counterexamplest &counterexamples, const goto_tracet &trace)
  {
    config.convert(counterexamples, trace);
  }
};

class danger_config_assertiont
{
  danger_verify_configt &config;
  goto_functionst &gf;
public:
  typedef danger_verify_configt::counterexamplet counterexamplet;
  typedef danger_verify_configt::counterexamplest counterexamplest;
  typedef danger_verify_configt::candidatet candidatet;

  danger_config_assertiont(danger_verify_configt &config) :
      config(config), gf(config.get_goto_functions())
  {
  }

  void process(const candidatet &candidate)
  {
    force_assertion_violation(gf, config.get_number_of_loops());
  }

  const symbol_tablet &get_symbol_table()
  {
    return config.get_symbol_table();
  }

  const goto_functionst &get_goto_functions()
  {
    return gf;
  }

  void convert(counterexamplest &counterexamples, const goto_tracet &trace)
  {
    config.convert(counterexamples, trace);
  }
};

template<class configt>
bool run_bmc(danger_verify_configt::counterexamplest &ces,
    const optionst &options, danger_verify_configt &config,
    const parallel_danger_verify_taskt::candidatet &candidate)
{
  configt cfg(config);
  cegis_symex_verifyt<configt> bmc(options, cfg);
  bmc.verify(candidate);
  std::copy(bmc.counterexamples_begin(), bmc.counterexamples_end(),
      std::back_inserter(ces));
  return bmc.success();
}

class ce_to_irept
{
  irept &result;
public:
  ce_to_irept(irept &result) :
      result(result)
  {
  }

  void operator()(
      const danger_verify_configt::counterexamplet::value_type &entry)
  {
    result.set(entry.first, entry.second);
  }
};

void to_irep(irept &result, const danger_verify_configt::counterexamplet &ce)
{
  const ce_to_irept convert(result);
  std::for_each(ce.begin(), ce.end(), convert);
}

class ces_to_irept
{
  irept &result;
public:
  ces_to_irept(irept &result) :
      result(result)
  {
  }

  void operator()(const danger_verify_configt::counterexamplet &ce)
  {
    irept converted;
    to_irep(converted, ce);
    result.move_to_sub(converted);
  }
};

const char RESULT[]="__CPROVER_danger_result";

void to_irep(irept &result, const bool success,
    const danger_verify_configt::counterexamplest &ces)
{
  result.set(RESULT, success);
  const ces_to_irept convert(result);
  std::for_each(ces.begin(), ces.end(), convert);
}

void from_irep(danger_verify_configt::counterexamplet &ce, const irept &result)
{
  forall_named_irep(it, result.get_named_sub()){
  const exprt &expr=static_cast<const exprt &>(it->second);
  ce.insert(std::make_pair(it->first, expr));
}
}

void from_irep(bool &success, danger_verify_configt::counterexamplest &ces,
    const irept &result)
{
  success=result.get_bool(RESULT);
  forall_irep(it, result.get_sub()){
  ces.push_back(danger_verify_configt::counterexamplet());
  danger_verify_configt::counterexamplet &ce=ces.back();
  from_irep(ce, *it);
}
}
}

void parallel_danger_verify_taskt::operator()()
{
  switch (mode)
  {
  case modet::FULL:
    success=run_bmc<danger_config_fullt>(new_ces, options, config, candidate);
    break;
  case modet::ASSERTION:
    success=run_bmc<danger_config_assertiont>(new_ces, options, config, candidate);
    break;
  default:
    success=run_bmc<danger_config_rankingt>(new_ces, options, config, candidate);
    break;
  }
  irept package;
  to_irep(package, success, new_ces);
#ifndef _WIN32
  pipe.close_read();
  pipe.send(package);
  pipe.close_write();
#endif
}

void parallel_danger_verify_taskt::read_counterexamples(bool &success,
counterexamplest &counterexamples)
{
  irept package;
#ifndef _WIN32
  pipe.receive(package);
  pipe.close_read();
#endif
  from_irep(this->success, new_ces, package);
  std::copy(new_ces.begin(), new_ces.end(), std::inserter(counterexamples, counterexamples.end()));
  success=this->success;
}

parallel_danger_verify_poolt::parallel_danger_verify_poolt(
    counterexamplest &counterexamples,
    const optionst &options,
    danger_verify_configt &config,
    const candidatet &candidate) : ces(counterexamples), options(options), config(config), candidate(candidate)
{
}

parallel_danger_verify_poolt::~parallel_danger_verify_poolt()
{
}

void parallel_danger_verify_poolt::schedule(parallel_danger_verify_taskt::modet mode)
{
  tasks.push_back(parallel_danger_verify_taskt(options, config, candidate, mode));
  parallel_danger_verify_taskt &task=tasks.back();
#ifndef _WIN32
  const pid_t child_pid=fork();
  if (child_pid) return task.set_parent_mode(child_pid);
#endif
  task();
#ifndef _WIN32
  exit(EXIT_SUCCESS);
#endif
}

namespace
{
class joint
{
  bool &success;
  parallel_danger_verify_poolt::counterexamplest &counterexamples;
public:
  joint(bool &success, parallel_danger_verify_poolt::counterexamplest &counterexamples) :
    success(success), counterexamples(counterexamples)
{
}

void operator()(parallel_danger_verify_taskt &task) const
{
#ifndef _WIN32
  int status;
  waitpid(task.get_child_pid(), &status, 0);
#endif
  bool success=false;
  task.read_counterexamples(success, counterexamples);
  if (!success) this->success=false;
}
};
}

bool parallel_danger_verify_poolt::join()
{
  bool success=true;
  const joint join(success, ces);
  std::for_each(tasks.begin(), tasks.end(), join);
  return success;
}
