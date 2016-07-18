#ifndef CPROVER_PRINT_LOCKS_ANALYSIS_CS_H
#define CPROVER_PRINT_LOCKS_ANALYSIS_CS_H

#include <analyses/ai_cs.h>
#include <util/misc_utils.h>

// bad, I know
typedef std::map<ai_cs_stackt, unsigned> thread_mapt;
thread_mapt thread_map;

class print_locks_domain_cst:public ai_cs_domain_baset
{
public:

  virtual bool merge(
    const ai_cs_domain_baset &other,
    locationt from,
    locationt to,
    const ai_cs_stackt &stack)
  {
    return false;
  }

  virtual bool merge_shared(
    const ai_cs_domain_baset &other,
    locationt from, locationt to,
    const namespacet &ns)
  {
    return false;
  }

  virtual void transform(
    locationt from_l,
    locationt to_l,
    const ai_cs_stackt &stack,
    ai_cs_baset &ai,
    const namespacet &ns)
  {
    if(!from_l->is_function_call())
      return;

    irep_idt id=misc::get_function_name(from_l);

    if(id2string(id)!=config.ansi_c.lock_function)
      return;

    ai_cs_baset::thread_idt thread_id=stack;
    thread_id.remove_top_calls();

    unsigned thread_num;

    thread_mapt::const_iterator it=thread_map.find(thread_id);
    if(it!=thread_map.end())
    {
      thread_num=it->second;
    }
    else
    {
      thread_num=thread_map.size();
      thread_map[thread_id]=thread_num;
    }

    std::cout << "Stack: " << stack << std::endl;
    std::cout << "Thread num: " << thread_num << std::endl;
    std::cout << "Caller: " << from_l->function << std::endl;

#if 0
    const code_function_callt &code=to_code_function_call(from_l->code);
    const exprt &expr=code.arguments()[0];
    std::cout << "Lock call arg: " << expr << std::endl;
    std::cout << "Call:\n" << from_l->code.pretty() << std::endl;
#endif

    std::cout << "========" << std::endl;
  }

  virtual void output(
    std::ostream &out,
    const ai_cs_baset &ai,
    const namespacet &ns) const
  {
  }

  virtual void make_bottom()
  {
  }

  virtual void make_top()
  {
  }
};

#endif
