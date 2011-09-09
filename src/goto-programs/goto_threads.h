/*******************************************************************\

Module: Threaded Goto Programs

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_GOTO_THREADS_H
#define CPROVER_GOTO_THREADS_H

#if 0 // this file is going away
#include <iostream>

#include <std_code.h>
#include <options.h>
#include <message.h>

#include "goto_program.h"

class goto_threadt
{
public:
  goto_programt goto_program;
  
  void swap(goto_threadt &thread)
  {
    thread.goto_program.swap(goto_program);
  }
};

// use list, the targets need to be stable
class goto_threadst
{
public:
  typedef std::list<goto_threadt> thread_listt;
  thread_listt thread_list;
  
  void clear()
  {
    thread_list.clear();
  }
  
  void output(
    const namespacet &ns,
    std::ostream &out);
};

#define forall_goto_threads(it, threads) \
  for(goto_threadst::thread_listt::const_iterator it=(threads).thread_list.begin(); \
      it!=(threads).thread_list.end(); it++)

#define Forall_goto_threads(it, threads) \
  for(goto_threadst::thread_listt::iterator it=(threads).thread_list.begin(); \
      it!=(threads).thread_list.end(); it++)

#define forall_goto_thread_list(it, thread_list) \
  for(goto_threadst::thread_listt::const_iterator it=(thread_list).begin(); \
      it!=(thread_list).end(); it++)

#define Forall_goto_thread_list(it, thread_list) \
  for(goto_threadst::thread_listt::iterator it=(threads_list).begin(); \
      it!=(thread_list).end(); it++)

// convert everyting starting from "main"
void goto_convert(
  contextt &context,
  const optionst &options,
  goto_threadst &goto_threads,
  message_handlert &message_handler);
#endif

#endif
