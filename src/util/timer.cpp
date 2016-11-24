/*******************************************************************\

Module: Time Stopping

Author:

Date:

\*******************************************************************/

#include <sstream>
#include <cassert>

#include "timer.h"

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

timert::~timert()
{      
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void timert::start()
{
  assert(!started);
  started = true;

  _start_time = current_time();
  nr_starts++;
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void timert::stop()
{
  assert(started);
  started = false;

  _latest_time = current_time() - _start_time;
  _total_time += _latest_time;
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void timert::clear()
{
  _total_time.clear();
  _start_time.clear();
}   
