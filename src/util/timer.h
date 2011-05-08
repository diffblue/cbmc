#ifndef CPROVER_TIMER_H
#define CPROVER_TIMER_H

#include "util/time_stopping.h"

class timert
{
private:
  fine_timet _total_time;
  fine_timet _start_time;
  fine_timet _latest_time;
  long nr_starts;
  bool started;

  public:
  timert()
     : _total_time(0), _start_time(0), _latest_time(0),
        nr_starts(0), started(false)
  {
  }

  virtual ~timert();

  virtual void start();
  virtual void stop();
  virtual void clear();

  virtual fine_timet total_time();
  virtual fine_timet latest_time();
  virtual long number_starts();

  std::string output_total_time();
  std::string output_latest_time();
  
  friend std::ostream& operator<< (std::ostream &out, const timert &timer);
};

std::ostream& operator<< (std::ostream &out, const timert &timer);

#endif /*CPROVER_TIMER_H*/
