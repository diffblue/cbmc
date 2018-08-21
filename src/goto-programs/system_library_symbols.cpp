/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley

\*******************************************************************/

/// \file
/// Goto Programs

#include "system_library_symbols.h"
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/suffix.h>
#include <util/symbol.h>
#include <util/type.h>
#include <sstream>

system_library_symbolst::system_library_symbolst(bool init):
  use_all_headers(false)
{
  if(init)
    init_system_library_map();
}

/// To generate a map of header file names -> list of symbols The symbol names
/// are reserved as the header and source files will be compiled in to the goto
/// program.
void system_library_symbolst::init_system_library_map()
{
  // ctype.h
  std::list<irep_idt> ctype_syms=
  {
    "isalnum", "isalpha", "isblank", "iscntrl", "isdigit", "isgraph",
    "islower", "isprint", "ispunct", "isspace", "isupper", "isxdigit",
    "tolower", "toupper"
  };
  add_to_system_library("ctype.h", ctype_syms);

  // fcntl.h
  std::list<irep_idt> fcntl_syms=
  {
    "creat", "fcntl", "open"
  };
  add_to_system_library("fcntl.h", fcntl_syms);

  // locale.h
  std::list<irep_idt> locale_syms=
  {
    "setlocale"
  };
  add_to_system_library("locale.h", locale_syms);

  // math.h
  std::list<irep_idt> math_syms=
  {
    "acos", "acosh", "asin", "asinh", "atan", "atan2", "atanh",
    "cbrt", "ceil", "copysign", "cos", "cosh", "erf", "erfc", "exp",
    "exp2", "expm1", "fabs", "fdim", "floor", "fma", "fmax", "fmin",
    "fmod", "fpclassify", "fpclassifyl", "fpclassifyf", "frexp",
    "hypot", "ilogb", "isfinite", "isinf", "isnan", "isnormal",
    "j0", "j1", "jn", "ldexp", "lgamma", "llrint", "llround", "log",
    "log10", "log1p", "log2", "logb", "lrint", "lround", "modf", "nan",
    "nearbyint", "nextafter", "pow", "remainder", "remquo", "rint",
    "round", "scalbln", "scalbn", "signbit", "sin", "sinh", "sqrt",
    "tan", "tanh", "tgamma", "trunc", "y0", "y1", "yn", "isinff",
    "isinfl", "isnanf", "isnanl"
  };
  add_to_system_library("math.h", math_syms);

  // for some reason the math functions can sometimes be prefixed with
  // a double underscore
  std::list<irep_idt> underscore_math_syms;
  for(const irep_idt &math_sym : math_syms)
  {
    std::ostringstream underscore_id;
    underscore_id << "__" << math_sym;
    underscore_math_syms.push_back(irep_idt(underscore_id.str()));
  }
  add_to_system_library("math.h", underscore_math_syms);

  // pthread.h
  std::list<irep_idt> pthread_syms=
  {
    "pthread_cleanup_pop", "pthread_cleanup_push",
    "pthread_cond_broadcast", "pthread_cond_destroy",
    "pthread_cond_init", "pthread_cond_signal",
    "pthread_cond_timedwait", "pthread_cond_wait", "pthread_create",
    "pthread_detach", "pthread_equal", "pthread_exit",
    "pthread_getspecific", "pthread_join", "pthread_key_delete",
    "pthread_mutex_destroy", "pthread_mutex_init",
    "pthread_mutex_lock", "pthread_mutex_trylock",
    "pthread_mutex_unlock", "pthread_once", "pthread_rwlock_destroy",
    "pthread_rwlock_init", "pthread_rwlock_rdlock",
    "pthread_rwlock_unlock", "pthread_rwlock_wrlock",
    "pthread_rwlockattr_destroy", "pthread_rwlockattr_getpshared",
    "pthread_rwlockattr_init", "pthread_rwlockattr_setpshared",
    "pthread_self", "pthread_setspecific",
    /* non-public struct types */
    "tag-__pthread_internal_list", "tag-__pthread_mutex_s",
    "pthread_mutex_t"
  };
  add_to_system_library("pthread.h", pthread_syms);

  // setjmp.h
  std::list<irep_idt> setjmp_syms=
  {
    "_longjmp", "_setjmp", "jmp_buf", "longjmp", "longjmperror", "setjmp",
    "siglongjmp", "sigsetjmp"
  };
  add_to_system_library("setjmp.h", setjmp_syms);

  // stdio.h
  std::list<irep_idt> stdio_syms=
  {
    "asprintf", "clearerr", "fclose", "fdopen", "feof", "ferror",
    "fflush", "fgetc", "fgetln", "fgetpos", "fgets", "fgetwc",
    "fgetws", "fileno", "fopen", "fprintf", "fpurge", "fputc",
    "fputs", "fputwc", "fputws", "fread", "freopen", "fropen",
    "fscanf", "fseek", "fsetpos", "ftell", "funopen", "fwide",
    "fwopen", "fwprintf", "fwrite", "getc", "getchar", "getdelim",
    "getline", "gets", "getw", "getwc", "getwchar", "mkdtemp",
    "mkstemp", "mktemp", "perror", "printf", "putc", "putchar",
    "puts", "putw", "putwc", "putwchar", "remove", "rewind", "scanf",
    "setbuf", "setbuffer", "setlinebuf", "setvbuf", "snprintf",
    "sprintf", "sscanf", "swprintf", "sys_errlist",
    "sys_nerr", "tempnam", "tmpfile", "tmpnam", "ungetc", "ungetwc",
    "vasprintf", "vfprintf", "vfscanf", "vfwprintf", "vprintf",
    "vscanf", "vsnprintf", "vsprintf", "vsscanf", "vswprintf",
    "vwprintf", "wprintf",
    /* non-public struct types */
    "tag-__sFILE", "tag-__sbuf", // OS X
    "tag-_IO_FILE", "tag-_IO_marker", // Linux
  };
  add_to_system_library("stdio.h", stdio_syms);

  // stdlib.h
  std::list<irep_idt> stdlib_syms=
  {
    "abort", "abs", "atexit", "atof", "atoi", "atol", "atoll",
    "bsearch", "calloc", "div", "exit", "free", "getenv", "labs",
    "ldiv", "llabs", "lldiv", "malloc", "mblen", "mbstowcs", "mbtowc",
    "qsort", "rand", "realloc", "srand", "strtod", "strtof", "strtol",
    "strtold", "strtoll", "strtoul", "strtoull", "system", "wcstombs",
    "wctomb"
  };
  add_to_system_library("stdlib.h", stdlib_syms);

  // string.h
  std::list<irep_idt> string_syms=
  {
    "strcat", "strncat", "strchr", "strrchr", "strcmp", "strncmp",
    "strcpy", "strncpy", "strerror", "strlen", "strpbrk", "strspn",
    "strcspn", "strstr", "strtok", "strcasecmp", "strncasecmp", "strdup",
    "memset"
  };
  add_to_system_library("string.h", string_syms);

  // time.h
  std::list<irep_idt> time_syms=
  {
    "asctime", "asctime_r", "ctime", "ctime_r", "difftime", "gmtime",
    "gmtime_r", "localtime", "localtime_r", "mktime", "strftime",
    /* non-public struct types */
    "tag-timespec", "tag-timeval", "tag-tm"
  };
  add_to_system_library("time.h", time_syms);

  // unistd.h
  std::list<irep_idt> unistd_syms=
  {
    "_exit", "access", "alarm", "chdir", "chown", "close", "dup",
    "dup2", "execl", "execle", "execlp", "execv", "execve", "execvp",
    "fork", "fpathconf", "getcwd", "getegid", "geteuid", "getgid",
    "getgroups", "getlogin", "getpgrp", "getpid", "getppid", "getuid",
    "isatty", "link", "lseek", "pathconf", "pause", "pipe", "read",
    "rmdir", "setgid", "setpgid", "setsid", "setuid", "sleep",
    "sysconf", "tcgetpgrp", "tcsetpgrp", "ttyname", "ttyname_r",
    "unlink", "write"
  };
  add_to_system_library("unistd.h", unistd_syms);

  // sys/select.h
  std::list<irep_idt> sys_select_syms=
  {
    "select",
    /* non-public struct types */
    "fd_set"
  };
  add_to_system_library("sys/select.h", sys_select_syms);

  // sys/socket.h
  std::list<irep_idt> sys_socket_syms=
  {
    "accept", "bind", "connect",
    /* non-public struct types */
    "tag-sockaddr"
  };
  add_to_system_library("sys/socket.h", sys_socket_syms);

  // sys/stat.h
  std::list<irep_idt> sys_stat_syms=
  {
    "fstat", "lstat", "stat",
    /* non-public struct types */
    "tag-stat"
  };
  add_to_system_library("sys/stat.h", sys_stat_syms);

  std::list<irep_idt> fenv_syms=
  {
    "fenv_t", "fexcept_t", "feclearexcept", "fegetexceptflag",
    "feraiseexcept", "fesetexceptflag", "fetestexcept",
    "fegetround", "fesetround", "fegetenv", "feholdexcept",
    "fesetenv", "feupdateenv"
  };
  add_to_system_library("fenv.h", fenv_syms);

  std::list<irep_idt> errno_syms=
  {
    "__error", "__errno_location", "__errno"
  };
  add_to_system_library("errno.h", errno_syms);

#if 0
  // sys/types.h
  std::list<irep_idt> sys_types_syms=
  {
  };
  add_to_system_library("sys/types.h", sys_types_syms);
#endif

  // sys/wait.h
  std::list<irep_idt> sys_wait_syms=
  {
    "wait", "waitpid"
  };
  add_to_system_library("sys/wait.h", sys_wait_syms);
}

/// To add the symbols from a specific header file to the system library map.
/// The symbol is used as the key so that we can easily look up symbols.
/// \param header_file: the name of the header file the symbol came from
/// \param symbols: a list of the names of the symbols in the header file
void system_library_symbolst::add_to_system_library(
  irep_idt header_file,
  std::list<irep_idt> symbols)
{
  for(const irep_idt &symbol : symbols)
  {
    system_library_map[symbol]=header_file;
  }
}

/// Helper function to call `is_symbol_internal_symbol` on a nameless
/// fake symbol with the given type, to determine whether the type alone
/// is sufficient to classify a symbol of that type as internal.
/// \param type: the type to check
/// \param [out] out_system_headers: specific system headers that need to be
///   included
/// \return True if the type is an internal type
bool system_library_symbolst::is_type_internal(
  const typet &type,
  std::set<std::string> &out_system_headers) const
{
  symbolt symbol;
  symbol.type=type;
  return is_symbol_internal_symbol(symbol, out_system_headers);
}

/// To find out if a symbol is an internal symbol.
/// \param symbol: the symbol to check
/// \param [out] out_system_headers: specific system headers that need to be
///   included
/// \return True if the symbol is an internal symbol
bool system_library_symbolst::is_symbol_internal_symbol(
  const symbolt &symbol,
  std::set<std::string> &out_system_headers) const
{
  const std::string &name_str=id2string(symbol.name);

  if(has_prefix(name_str, CPROVER_PREFIX) ||
     name_str=="__func__" ||
     name_str=="__FUNCTION__" ||
     name_str=="__PRETTY_FUNCTION__" ||
     name_str=="argc'" ||
     name_str=="argv'" ||
     name_str=="envp'" ||
     name_str=="envp_size'")
    return true;

  if(has_suffix(name_str, "$object"))
    return true;

  // exclude nondet instructions
  if(has_prefix(name_str, "nondet_"))
  {
    return true;
  }

  if(has_prefix(name_str, "__VERIFIER"))
  {
    return true;
  }

  const std::string &file_str=id2string(symbol.location.get_file());

  // don't dump internal GCC builtins
  if(has_prefix(file_str, "gcc_builtin_headers_") &&
     has_prefix(name_str, "__builtin_"))
    return true;

  if(name_str=="__builtin_va_start" ||
     name_str=="__builtin_va_end" ||
     symbol.name==ID_gcc_builtin_va_arg)
  {
    out_system_headers.insert("stdarg.h");
    return true;
  }

  // don't dump asserts
  else if(name_str=="__assert_fail" ||
          name_str=="_assert" ||
          name_str=="__assert_c99" ||
          name_str=="_wassert")
  {
    return true;
  }

  const auto &it=system_library_map.find(symbol.name);

  if(it!=system_library_map.end())
  {
    out_system_headers.insert(id2string(it->second));
    return true;
  }

  if(use_all_headers &&
     has_prefix(file_str, "/usr/include/"))
  {
    if(file_str.find("/bits/")==std::string::npos)
    {
      // Do not include transitive includes of system headers!
      std::string::size_type prefix_len=std::string("/usr/include/").size();
      out_system_headers.insert(file_str.substr(prefix_len));
    }

    return true;
  }

  return false;
}
