/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifdef __APPLE__
#include <mach/task.h>
#include <mach/mach_init.h>
#include <malloc/malloc.h>
#endif

#ifdef __linux__
#include <malloc.h>
#endif

#ifdef _WIN32
#include <windows.h>
#include <psapi.h>
#endif

#include <ostream>

#include "memory_info.h"

/*******************************************************************\

Function: memory_info

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_info(std::ostream &out)
{
  #ifdef __linux__
  struct mallinfo m = mallinfo();
  out << "  non-mmapped space allocated from system: " << m.arena << "\n";
  out << "  number of free chunks: " << m.ordblks << "\n";
  out << "  number of fastbin blocks: " << m.smblks << "\n";
  out << "  number of mmapped regions: " << m.hblks << "\n";
  out << "  space in mmapped regions: " << m.hblkhd << "\n";
  out << "  maximum total allocated space: " << m.usmblks << "\n";
  out << "  space available in freed fastbin blocks: " << m.fsmblks << "\n";
  out << "  total allocated space: " << m.uordblks << "\n";
  out << "  total free space: " << m.fordblks << "\n";
  #endif
  
  #ifdef _WIN32
  #if 0
  PROCESS_MEMORY_COUNTERS pmc;
  if(GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc)))
  {
    out << "  PeakWorkingSetSize: " << pmc.PeakWorkingSetSize << "\n";
    out << "  WorkingSetSize: " << pmc.WorkingSetSize << "\n";
  }
  #endif
  #endif
  
  #ifdef __APPLE__
  struct task_basic_info t_info;
  mach_msg_type_number_t t_info_count = TASK_BASIC_INFO_COUNT;
  task_info(current_task(), TASK_BASIC_INFO, (task_info_t)&t_info, &t_info_count);
  out << "  virtual size: " << (double)t_info.virtual_size/1000000 << "m\n";

  malloc_statistics_t t;
  malloc_zone_statistics(NULL, &t);
  out << "  max_size_in_use: " << (double)t.max_size_in_use/1000000 << "m\n";
  out << "  size_allocated: " << (double)t.size_allocated/1000000 << "m\n";
  #endif
}
