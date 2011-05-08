/*******************************************************************\

Module: GOTO Threads

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <i2string.h>

#include "goto_convert_functions.h"
#include "goto_threads.h"
#include "remove_skip.h"
#include "goto_inline.h"
#include "goto_inline_class.h"

/*******************************************************************\

Function: goto_threadst::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_threadst::output(
  const namespacet &ns,
  std::ostream &out)
{
  unsigned thread_nr=0;

  forall_goto_thread_list(it, thread_list)
  {
    out << "******** THREAD: " << thread_nr << std::endl;
    it->goto_program.output(ns, "", out);
    thread_nr++;
    out << std::endl;
  }
}

/*******************************************************************\

   Class: goto_thread_convertt

 Purpose:

\*******************************************************************/

class goto_thread_convertt:public goto_inlinet
{
public:
  goto_thread_convertt(
    goto_threadst &_threads,
    goto_functionst &_goto_functions,
    const namespacet &_ns,
    message_handlert &_message_handler):
    goto_inlinet(_goto_functions, _ns, _message_handler),
    threads(_threads)
  {
  }
  
  void goto_convert(goto_programt &dest);

protected:
  goto_threadst &threads;
};

/*******************************************************************\

Function: goto_thread_convertt::goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_thread_convertt::goto_convert(goto_programt &dest)
{
  for(goto_programt::instructionst::iterator
      it=dest.instructions.begin();
      it!=dest.instructions.end();
      ) // no it++
  {
    if(it->is_other() || it->is_function_call())
    {
      inline_instruction(dest, true, it);
    }
    else if(it->is_start_thread())
    {
      #if 0
      std::string event=
        "start_thread_"+i2string(threads.thread_list.size());

      threads.thread_list.push_back(goto_threadt());
      goto_threadt &thread=threads.thread_list.back();

      assert(it->targets.size()==1);
      goto_programt::targett new_it=it->targets.front();

      goto_programt::targett next_it=it;
      next_it++;

      it->targets.clear();
      it->type=SYNC;
      it->event=event;
      
      goto_programt tmp;
      goto_programt::targett sync=tmp.add_instruction(SYNC);
      sync->event=event;
      sync->location=it->location;
      thread.goto_program.destructive_append(tmp);

      thread.goto_program.instructions.splice(
        thread.goto_program.instructions.end(),
        dest.instructions, next_it, new_it);
        
      it=new_it;
      
      // do this recursively on the new thread
      goto_convert(thread.goto_program);
      #endif
    }
    else
      it++;
  }

  remove_skip(dest);  
  dest.update();
}

/*******************************************************************\

Function: goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert(
  contextt &context,
  const optionst &options,
  goto_threadst &goto_threads,
  message_handlert &message_handler)
{
  goto_functionst goto_functions;

  goto_convert(
    context,
    options,
    goto_functions,
    message_handler);
  
  goto_threads.thread_list.push_back(goto_threadt());
  goto_threadt &thread=goto_threads.thread_list.back();
  
  {
    // find main
    goto_functionst::function_mapt::iterator it=
      goto_functions.function_map.find(ID_main);
      
    if(it==goto_functions.function_map.end())
      return;
    
    thread.goto_program.swap(it->second.body);
  }
  
  const namespacet ns(context);
  goto_thread_convertt goto_thread_convert(goto_threads, goto_functions, ns, message_handler);

  try
  {
    goto_thread_convert.goto_convert(thread.goto_program);
  }

  catch(int)
  {
    goto_thread_convert.error();
  }

  catch(const char *e)
  {
    goto_thread_convert.error(e);
  }

  catch(const std::string &e)
  {
    goto_thread_convert.error(e);
  }

  if(goto_thread_convert.get_error_found())
    throw 0;
}
