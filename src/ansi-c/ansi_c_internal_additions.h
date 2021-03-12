/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_ANSI_C_INTERNAL_ADDITIONS_H
#define CPROVER_ANSI_C_ANSI_C_INTERNAL_ADDITIONS_H

#include <string>

void ansi_c_internal_additions(std::string &code);
void ansi_c_architecture_strings(std::string &code);

extern const char clang_builtin_headers[];
extern const char cprover_builtin_headers[];
extern const char gcc_builtin_headers_types[];
extern const char gcc_builtin_headers_generic[];
extern const char gcc_builtin_headers_math[];
extern const char gcc_builtin_headers_mem_string[];
extern const char gcc_builtin_headers_omp[];
extern const char gcc_builtin_headers_tm[];
extern const char gcc_builtin_headers_ubsan[];
extern const char gcc_builtin_headers_ia32[];
extern const char gcc_builtin_headers_ia32_2[];
extern const char gcc_builtin_headers_ia32_3[];
extern const char gcc_builtin_headers_ia32_4[];
extern const char gcc_builtin_headers_ia32_5[];
extern const char gcc_builtin_headers_alpha[];
extern const char gcc_builtin_headers_arm[];
extern const char gcc_builtin_headers_mips[];
extern const char gcc_builtin_headers_power[];
extern const char arm_builtin_headers[];
extern const char cw_builtin_headers[];
extern const char windows_builtin_headers[];

#endif // CPROVER_ANSI_C_ANSI_C_INTERNAL_ADDITIONS_H
