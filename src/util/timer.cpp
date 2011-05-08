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
  _total_time = 0;
  _start_time = 0;
}   

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

fine_timet timert::total_time()
{
  return _total_time;
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

fine_timet timert::latest_time()
{
  return _latest_time;
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

long timert::number_starts()
{
  return nr_starts;
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string timert::output_total_time()
{
  return time2string(_total_time);
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string timert::output_latest_time()
{
  return time2string(_latest_time);
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<< (std::ostream &out, const timert &timer)
{
  out << time2string(timer._total_time);
  return out;
}
