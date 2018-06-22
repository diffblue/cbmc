/*******************************************************************\

Module: Timestamps

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "timestamper.h"

#include <chrono>
#include <cstdlib>
#include <iomanip>
#include <sstream>

#include "invariant.h"

std::unique_ptr<const timestampert>
timestampert::make(timestampert::clockt clock_type)
{
#ifdef _WIN32
  (void)clock_type; // unused parameter
  return std::unique_ptr<const timestampert>(new timestampert());
#else
  switch(clock_type)
  {
  case timestampert::clockt::NONE:
    return std::unique_ptr<const timestampert>(new timestampert());
  case timestampert::clockt::MONOTONIC:
    return std::unique_ptr<const monotonic_timestampert>(
      new monotonic_timestampert());
  case timestampert::clockt::WALL_CLOCK:
    return std::unique_ptr<const wall_clock_timestampert>(
      new wall_clock_timestampert());
  }
  UNREACHABLE;
#endif
}

#ifndef _WIN32
std::string monotonic_timestampert::stamp() const
{
  std::chrono::time_point<std::chrono::steady_clock, std::chrono::microseconds>
    time_stamp = std::chrono::time_point_cast<std::chrono::microseconds>(
      std::chrono::steady_clock::now());

  auto cnt = time_stamp.time_since_epoch().count();
  std::lldiv_t divmod = lldiv(cnt, 1000000);

  std::stringstream ss;
  ss << divmod.quot << "." << std::setfill('0') << std::setw(6) << divmod.rem;
  return ss.str();
}

#define WALL_FORMAT "%Y-%m-%dT%H:%M:%S."

std::string wall_clock_timestampert::stamp() const
{
  std::chrono::time_point<std::chrono::system_clock, std::chrono::microseconds>
    time_stamp = std::chrono::time_point_cast<std::chrono::microseconds>(
      std::chrono::system_clock::now());

  unsigned u_seconds = time_stamp.time_since_epoch().count() % 1000000;

  std::time_t tt = std::chrono::system_clock::to_time_t(time_stamp);
  std::tm local = *std::localtime(&tt);

  std::stringstream ss;
  ss << std::put_time(&local, WALL_FORMAT) << std::setfill('0') << std::setw(6)
     << u_seconds;
  return ss.str();
}
#endif
