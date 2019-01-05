/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "memory_info.h"

#ifdef __APPLE__
#include <mach/task.h>
#include <mach/mach_init.h>
#include <malloc/malloc.h>
#endif

#ifdef __linux__
#include <malloc.h>
#endif

#ifdef _WIN32
#include <util/pragma_push.def>
#ifdef _MSC_VER
#pragma warning(disable:4668)
  // using #if/#elif on undefined macro
#endif
#include <windows.h>
#include <psapi.h>
#include <util/pragma_pop.def>
#endif

#include <ostream>

void memory_info(std::ostream &out)
{
#if defined(__linux__) && defined(__GLIBC__)
  // NOLINTNEXTLINE(readability/identifiers)
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
#elif defined(_WIN32)
  PROCESS_MEMORY_COUNTERS pmc;
  if(GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc)))
  {
    out << "  peak working set size [bytes]: " << pmc.PeakWorkingSetSize
        << "\n";
    out << "  current working set size [bytes]: " << pmc.WorkingSetSize << "\n";
  }
#elif defined(__APPLE__)
  // NOLINTNEXTLINE(readability/identifiers)
  struct task_basic_info t_info;
  mach_msg_type_number_t t_info_count = TASK_BASIC_INFO_COUNT;
  task_info(
    current_task(), TASK_BASIC_INFO, (task_info_t)&t_info, &t_info_count);
  out << "  virtual size: "
      << static_cast<double>(t_info.virtual_size)/1000000 << "m\n";

  malloc_statistics_t t;
  malloc_zone_statistics(NULL, &t);
  out << "  max_size_in_use: "
      << static_cast<double>(t.max_size_in_use)/1000000 << "m\n";
  out << "  size_allocated: "
      << static_cast<double>(t.size_allocated)/1000000 << "m\n";
#endif
}
