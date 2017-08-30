/*******************************************************************\

Module: Time Stopping

Author:

Date:

\*******************************************************************/

/// \file
/// Time Stopping

#include "timer.h"

#include <sstream>
#include <cassert>

timert::~timert()
{
}

void timert::start()
{
  assert(!started);
  started = true;

  _start_time = current_time();
  nr_starts++;
}

void timert::stop()
{
  assert(started);
  started = false;

  _latest_time = current_time() - _start_time;
  _total_time += _latest_time;
}

void timert::clear()
{
  _total_time.clear();
  _start_time.clear();
}
