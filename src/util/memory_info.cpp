/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifdef __APPLE__
#include <mach/task.h>
#include <mach/mach_init.h>
#endif

#ifdef __linux__
#include <malloc.h>
#endif

#ifdef _WIN32
#include <windows.h>
#endif

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
  out << "  non-mmapped space allocated from system: " << m.arena << std::endl;
  out << "  number of free chunks: " << m.ordblks << std::endl;
  out << "  number of fastbin blocks: " << m.smblks << std::endl;
  out << "  number of mmapped regions: " << m.hblks << std::endl;
  out << "  space in mmapped regions: " << m.hblkhd << std::endl;
  out << "  maximum total allocated space: " << m.usmblks << std::endl;
  out << "  space available in freed fastbin blocks: " << m.fsmblks << std::endl;
  out << "  total allocated space: " << m.uordblks << std::endl;
  out << "  total free space: " << m.fordblks << std::endl;
  #endif
  
  #ifdef _WIN32
  PROCESS_MEMORY_COUNTERS pmc;
  if(GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc)))
  {
    out << "  PeakWorkingSetSize: " << pmc.PeakWorkingSetSize << std::endl;
    out << "  WorkingSetSize: " << pmc.WorkingSetSize << std::endl;
  }
  #endif
  
  #ifdef __APPLE__
  struct task_basic_info t_info;
  mach_msg_type_number_t t_info_count = TASK_BASIC_INFO_COUNT;
  task_info(current_task(), TASK_BASIC_INFO, (task_info_t)&t_info, &t_info_count);
  out << "  virtual size: " << t_info.virtual_size/1000000 << "m" << std::endl;
  #endif
}
