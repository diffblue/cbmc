/*******************************************************************\

Module: Dump Goto-Program as C/C++ Source

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>
#include <cctype>

#include <util/config.h>
#include <util/prefix.h>
#include <util/suffix.h>
#include <util/find_symbols.h>
#include <util/base_type.h>
#include <util/i2string.h>
#include <util/cprover_prefix.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include "goto_program2code.h"
#include "dump_c_class.h"

#include "dump_c.h"

/*******************************************************************\

Function: operator<<

Inputs:

Outputs:

Purpose:

\*******************************************************************/

inline std::ostream &operator << (std::ostream &out, dump_ct &src)
{
  src(out);
  return out;
}

/*******************************************************************\

Function: dump_ct::operator()

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::operator()(std::ostream &os)
{
  std::stringstream func_decl_stream;
  std::stringstream compound_body_stream;
  std::stringstream global_var_stream;
  std::stringstream func_body_stream;
  local_static_declst local_static_decls;

  // add copies of struct types when ID_C_transparent_union is only
  // annotated to parameter
  symbol_tablet symbols_transparent;
  Forall_symbols(it, copied_symbol_table.symbols)
  {
    symbolt &symbol=it->second;

    if(symbol.type.id()!=ID_code) continue;

    code_typet &code_type=to_code_type(symbol.type);
    code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::iterator
        it2=parameters.begin();
        it2!=parameters.end();
        ++it2)
    {
      typet &type=it2->type();

      if(type.id()==ID_symbol &&
         type.get_bool(ID_C_transparent_union))
      {
        symbolt new_type_sym=
          ns.lookup(to_symbol_type(type).get_identifier());

        new_type_sym.name=id2string(new_type_sym.name)+"$transparent";
        new_type_sym.type.set(ID_C_transparent_union, true);

        // we might have it already, in which case this has no effect
        symbols_transparent.add(new_type_sym);

        to_symbol_type(type).set_identifier(new_type_sym.name);
        type.remove(ID_C_transparent_union);
      }
    }
  }
  forall_symbols(it, symbols_transparent.symbols)
    copied_symbol_table.add(it->second);

  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> unique_tagst;
  unique_tagst unique_tags;

  // add tags to anonymous union/struct/enum,
  // and prepare lexicographic order
  std::set<std::string> symbols_sorted;
  Forall_symbols(it, copied_symbol_table.symbols)
  {
    symbolt &symbol=it->second;
    bool tag_added=false;

    if((symbol.type.id()==ID_union || symbol.type.id()==ID_struct) &&
       symbol.type.get(ID_tag).empty())
    {
      assert(symbol.is_type);
      symbol.type.set(ID_tag, ID_anonymous);
      tag_added=true;
    }
    else if(symbol.type.id()==ID_c_enum &&
            symbol.type.find(ID_tag).get(ID_C_base_name).empty())
    {
      assert(symbol.is_type);
      symbol.type.add(ID_tag).set(ID_C_base_name, ID_anonymous);
      tag_added=true;
    }

    const std::string name_str=id2string(it->first);
    if(symbol.is_type &&
       (symbol.type.id()==ID_union ||
        symbol.type.id()==ID_struct ||
        symbol.type.id()==ID_c_enum))
    {
      std::string new_tag=symbol.type.id()==ID_c_enum?
        symbol.type.find(ID_tag).get_string(ID_C_base_name):
        symbol.type.get_string(ID_tag);

      std::string::size_type tag_pos=new_tag.rfind("tag-");
      if(tag_pos!=std::string::npos) new_tag.erase(0, tag_pos+4);
      const std::string new_tag_base=new_tag;

      for(std::pair<unique_tagst::iterator, bool>
          unique_entry=unique_tags.insert(std::make_pair(new_tag, 0));
          !unique_entry.second;
          unique_entry=unique_tags.insert(std::make_pair(new_tag, 0)))
      {
        new_tag=new_tag_base+"$"+
          i2string(unique_entry.first->second);
        ++(unique_entry.first->second);
      }

      if(symbol.type.id()==ID_c_enum)
      {
        symbol.type.add(ID_tag).set(ID_C_base_name, new_tag);
        symbol.base_name=new_tag;
      }
      else
        symbol.type.set(ID_tag, new_tag);
    }

    // we don't want to dump in full all definitions
    if(!tag_added && ignore(symbol))
      continue;

    if(!symbols_sorted.insert(name_str).second)
      assert(false);
  }

  // collect all declarations we might need, include local static variables
  bool skip_function_main=false;
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.is_type &&
       symbol.location.get_function().empty() &&
       (symbol.type.id()==ID_struct ||
        symbol.type.id()==ID_incomplete_struct ||
        symbol.type.id()==ID_union ||
        symbol.type.id()==ID_incomplete_union))
    {
      os << "// " << symbol.name << std::endl;
      os << "// " << symbol.location << std::endl;
      os << type_to_string(symbol.type) << ";\n\n";
    }
    else if(symbol.is_type &&
            symbol.location.get_function().empty() &&
            symbol.type.id()==ID_c_enum)
    {
      os << "// " << symbol.name << std::endl;
      os << "// " << symbol.location << std::endl;
      convert_compound_enum(symbol.type, os);
    }
    else if(symbol.is_static_lifetime && symbol.type.id()!=ID_code)
      convert_global_variable(
          symbol,
          global_var_stream,
          local_static_decls);
    else if(symbol.type.id()==ID_code)
    {
      goto_functionst::function_mapt::const_iterator func_entry=
        goto_functions.function_map.find(symbol.name);

      if(func_entry!=goto_functions.function_map.end() &&
         func_entry->second.body_available &&
         (symbol.name==ID_main ||
          (!config.main.empty() && symbol.name==config.main)))
        skip_function_main=true;
    }
  }

  // function declarations and definitions
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.type.id()!=ID_code) continue;

    convert_function_declaration(
      symbol,
      skip_function_main,
      func_decl_stream,
      func_body_stream,
      local_static_decls);
  }

  // (possibly modified) compound types
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.is_type &&
        (symbol.type.id()==ID_struct ||
         symbol.type.id()==ID_incomplete_struct ||
         symbol.type.id()==ID_union ||
         symbol.type.id()==ID_incomplete_union))
      convert_compound_declaration(
          symbol,
          compound_body_stream);
  }

  for(std::set<std::string>::const_iterator
      it=system_headers.begin();
      it!=system_headers.end();
      ++it)
    os << "#include <" << *it << ">" << std::endl;
  if(!system_headers.empty()) os << std::endl;

  if(global_var_stream.str().find("NULL")!=std::string::npos ||
     func_body_stream.str().find("NULL")!=std::string::npos)
  {
    os << "#ifndef NULL" << std::endl
       << "#define NULL ((void*)0)" << std::endl
       << "#endif" << std::endl;
    os << std::endl;
  }
  if(func_body_stream.str().find("FENCE")!=std::string::npos)
  {
    os << "#ifndef FENCE" << std::endl
       << "#define FENCE(x) ((void)0)" << std::endl
       << "#endif" << std::endl;
    os << std::endl;
  }
  if(func_body_stream.str().find("IEEE_FLOAT_")!=std::string::npos)
  {
    os << "#ifndef IEEE_FLOAT_EQUAL" << std::endl
       << "#define IEEE_FLOAT_EQUAL(x,y) ((x)==(y))" << std::endl
       << "#endif" << std::endl;
    os << "#ifndef IEEE_FLOAT_NOTEQUAL" << std::endl
       << "#define IEEE_FLOAT_NOTEQUAL(x,y) ((x)!=(y))" << std::endl
       << "#endif" << std::endl;
    os << std::endl;
  }

  if(!func_decl_stream.str().empty())
    os << func_decl_stream.str() << std::endl;
  if(!compound_body_stream.str().empty())
    os << compound_body_stream.str() << std::endl;
  if(!global_var_stream.str().empty())
    os << global_var_stream.str() << std::endl;
  os << func_body_stream.str();
}

/*******************************************************************\

Function: dump_ct::convert_compound_declarations

Inputs:

Outputs:

Purpose: declare compound types

\*******************************************************************/

void dump_ct::convert_compound_declaration(
    const symbolt &symbol,
    std::ostream &os_body)
{
  if(!symbol.location.get_function().empty())
    return;

  // do compound type body
  if(symbol.type.id()==ID_struct ||
     symbol.type.id()==ID_union ||
     symbol.type.id()==ID_c_enum)
    convert_compound(symbol.type, true, os_body);
}

/*******************************************************************\

Function: dump_ct::convert_compound

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::convert_compound(
  const typet &type,
  bool recursive,
  std::ostream &os)
{
  if(type.id()==ID_symbol)
  {
    const symbolt &symbol=
      ns.lookup(to_symbol_type(type).get_identifier());
    assert(symbol.is_type);

    if(!ignore(symbol))
      convert_compound(symbol.type, recursive, os);
  }
  else if(type.id()==ID_c_enum_tag)
  {
    const symbolt &symbol=
      ns.lookup(to_c_enum_tag_type(type).get_identifier());
    assert(symbol.is_type);

    if(!ignore(symbol))
      convert_compound(symbol.type, recursive, os);
  }
  else if(type.id()==ID_array || type.id()==ID_pointer)
  {
    if(!recursive) return;

    convert_compound(type.subtype(), recursive, os);

    // sizeof may contain a type symbol that has to be declared first
    if(type.id()==ID_array)
    {
      find_symbols_sett syms;
      find_type_symbols(to_array_type(type).size(), syms);

      for(find_symbols_sett::const_iterator
          it=syms.begin();
          it!=syms.end();
          ++it)
        convert_compound(symbol_typet(*it), recursive, os);
    }
  }
  else if(type.id()==ID_struct || type.id()==ID_union)
    convert_compound(to_struct_union_type(type), recursive, os);
  else if(type.id()==ID_c_enum)
    convert_compound_enum(type, os);
}

/*******************************************************************\

Function: dump_ct::convert_compound

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::convert_compound(
  const struct_union_typet &type,
  bool recursive,
  std::ostream &os)
{
  const irep_idt &name=type.get(ID_tag);

  if(!converted.insert(name).second)
    return;

  const irept &bases = type.find(ID_bases);
  std::stringstream base_decls;
  forall_irep(parent_it, bases.get_sub())
  {
    assert(false);
    /*
    assert(parent_it->id() == ID_base);
    assert(parent_it->get(ID_type) == ID_symbol);

    const irep_idt &base_id=
      parent_it->find(ID_type).get(ID_identifier);
    const irep_idt &renamed_base_id=global_renaming[base_id];
    const symbolt &parsymb=ns.lookup(renamed_base_id);

    convert_compound_rec(parsymb.type, os);

    base_decls << id2string(renamed_base_id) +
      (parent_it+1==bases.get_sub().end()?"":", ");
      */
  }

  /*
  // for the constructor
  string constructor_args;
  string constructor_body;

  std::string component_name =  id2string(renaming[compo.get(ID_name)]);
  assert(component_name != "");

  if(it != struct_type.components().begin()) constructor_args += ", ";

  if(compo.type().id() == ID_pointer)
  constructor_args += type_to_string(compo.type()) + component_name;
  else
  constructor_args += "const " + type_to_string(compo.type()) + "& " + component_name;

  constructor_body += indent + indent + "this->"+component_name + " = " + component_name + ";\n";
  */

  std::stringstream struct_body;

  for(struct_union_typet::componentst::const_iterator
      it=type.components().begin();
      it!=type.components().end();
      it++)
  {
    const struct_typet::componentt &comp=*it;
    typet comp_type=ns.follow(comp.type());

    if(comp_type.id()==ID_code ||
       comp.get_bool(ID_from_base) ||
       comp.get_is_padding())
      continue;

    if(recursive && comp_type.id()!=ID_pointer)
      convert_compound(comp.type(), recursive, os);

    irep_idt comp_name=comp.get_name();

    struct_body << indent(1) << "// " << comp_name << std::endl;
    struct_body << indent(1);

    // component names such as "main" would collide with other objects in the
    // namespace
    std::string fake_unique_name="NO/SUCH/NS::"+id2string(comp_name);
    std::string s=make_decl(fake_unique_name, comp_type);
    assert(s.find("NO/SUCH/NS")==std::string::npos);

    if(comp_type.id()==ID_c_bit_field &&
       to_c_bit_field_type(comp_type).get_width()==0)
    {
      comp_name="";
      s=type_to_string(comp_type);
    }

    if(s.find("__CPROVER_bitvector")==std::string::npos)
    {
      struct_body << s;
    }
    else if(comp_type.id()==ID_signedbv)
    {
      const signedbv_typet &t=to_signedbv_type(comp_type);
      if(t.get_width()<=config.ansi_c.long_long_int_width)
        struct_body << "long long int " << comp_name
          << " : " << t.get_width();
      else if(language->id()=="cpp")
        struct_body << "__signedbv<" << t.get_width() << "> "
          << comp_name;
      else
        struct_body << s;
    }
    else if(comp_type.id()==ID_unsignedbv)
    {
      const unsignedbv_typet &t=to_unsignedbv_type(comp_type);
      if(t.get_width()<=config.ansi_c.long_long_int_width)
        struct_body << "unsigned long long " << comp_name
          << " : " << t.get_width();
      else if(language->id()=="cpp")
        struct_body << "__unsignedbv<" << t.get_width() << "> "
          << comp_name;
      else
        struct_body << s;
    }
    else
      assert(false);

    struct_body << ";" << std::endl;
  }

  os << type_to_string(type);
  if(!base_decls.str().empty())
  {
    assert(language->id()=="cpp");
    os << ": " << base_decls.str();
  }
  os << std::endl;
  os << "{" << std::endl;
  os << struct_body.str();

  /*
     if(!struct_type.components().empty())
     {
     os << indent << name << "(){}\n";
     os << indent << "explicit " << name
     << "(" + constructor_args + ")\n";
     os << indent << "{\n";
     os << constructor_body;
     os << indent << "}\n";
     }
     */

  os << "}";
  if(type.get_bool(ID_C_transparent_union))
    os << " __attribute__ ((__transparent_union__))";
  if(type.get_bool(ID_C_packed))
    os << " __attribute__ ((__packed__))";
  os << ";";
  os << std::endl;
  os << std::endl;
}

/*******************************************************************\

Function: dump_ct::convert_compound_enum

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::convert_compound_enum(
  const typet &type,
  std::ostream &os)
{
  assert(type.id()==ID_c_enum);

  const irept &tag=type.find(ID_tag);
  const irep_idt &name=tag.get(ID_C_base_name);

  if(tag.is_nil() ||
     !converted.insert(name).second)
    return;

  os << type_to_string(type);

  if(type.get_bool(ID_C_packed))
    os << " __attribute__ ((__packed__))";

  os << ";\n\n";

  const c_enum_typet::memberst &members=
    to_c_enum_type(type).members();
  for(c_enum_typet::memberst::const_iterator
      it=members.begin();
      it!=members.end();
      ++it)
    declared_enum_constants.insert(it->get_base_name());
}

/*******************************************************************\

Function: dump_ct::init_system_library_map

Inputs:

Outputs:

Purpose:

\*******************************************************************/

#define ADD_TO_SYSTEM_LIBRARY(v, header) \
  for(size_t i=0; i<sizeof(v)/sizeof(char*); ++i) \
    system_library_map.insert( \
      std::make_pair(v[i], header))

void dump_ct::init_system_library_map()
{
  // ctype.h
  const char* ctype_syms[]={
    "isalnum", "isalpha", "isblank", "iscntrl", "isdigit", "isgraph",
    "islower", "isprint", "ispunct", "isspace", "isupper", "isxdigit",
    "tolower", "toupper"
  };
  ADD_TO_SYSTEM_LIBRARY(ctype_syms, "ctype.h");

  // fcntl.h
  const char* fcntl_syms[]={
    "creat", "fcntl", "open"
  };
  ADD_TO_SYSTEM_LIBRARY(fcntl_syms, "fcntl.h");

  // locale.h
  const char* locale_syms[]={
    "setlocale"
  };
  ADD_TO_SYSTEM_LIBRARY(locale_syms, "locale.h");

  // math.h
  const char* math_syms[]={
    "acos", "acosh", "asin", "asinh", "atan", "atan2", "atanh",
    "cbrt", "ceil", "copysign", "cos", "cosh", "erf", "erfc", "exp",
    "exp2", "expm1", "fabs", "fdim", "floor", "fma", "fmax", "fmin",
    "fmod", "fpclassify", "frexp", "hypot", "ilogb", "isfinite",
    "isinf", "isnan", "isnormal", "j0", "j1", "jn", "ldexp", "lgamma",
    "llrint", "llround", "log", "log10", "log1p", "log2", "logb",
    "lrint", "lround", "modf", "nan", "nearbyint", "nextafter", "pow",
    "remainder", "remquo", "rint", "round", "scalbln", "scalbn",
    "signbit", "sin", "sinh", "sqrt", "tan", "tanh", "tgamma",
    "trunc", "y0", "y1", "yn"
  };
  ADD_TO_SYSTEM_LIBRARY(math_syms, "math.h");

  // pthread.h
  const char* pthread_syms[]={
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
    "pthread_self", "pthread_setspecific"
  };
  ADD_TO_SYSTEM_LIBRARY(pthread_syms, "pthread.h");

  // setjmp.h
  const char* setjmp_syms[]={
    "_longjmp", "_setjmp", "longjmp", "longjmperror", "setjmp",
    "siglongjmp", "sigsetjmp"
  };
  ADD_TO_SYSTEM_LIBRARY(setjmp_syms, "setjmp.h");

  // stdio.h
  const char* stdio_syms[]={
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
    "sprintf", "sscanf", "strerror", "swprintf", "sys_errlist",
    "sys_nerr", "tempnam", "tmpfile", "tmpnam", "ungetc", "ungetwc",
    "vasprintf", "vfprintf", "vfscanf", "vfwprintf", "vprintf",
    "vscanf", "vsnprintf", "vsprintf", "vsscanf", "vswprintf",
    "vwprintf", "wprintf",
    /* non-public struct types */
    "tag-__sFILE", "tag-__sbuf", // OS X
    "tag-_IO_FILE", "tag-_IO_marker", // Linux
  };
  ADD_TO_SYSTEM_LIBRARY(stdio_syms, "stdio.h");

  // stdlib.h
  const char* stdlib_syms[]={
    "abort", "abs", "atexit", "atof", "atoi", "atol", "atoll",
    "bsearch", "calloc", "div", "exit", "free", "getenv", "labs",
    "ldiv", "llabs", "lldiv", "malloc", "mblen", "mbstowcs", "mbtowc",
    "qsort", "rand", "realloc", "srand", "strtod", "strtof", "strtol",
    "strtold", "strtoll", "strtoul", "strtoull", "system", "wcstombs",
    "wctomb"
  };
  ADD_TO_SYSTEM_LIBRARY(stdlib_syms, "stdlib.h");

  // string.h
  const char* string_syms[]={
    "strcat", "strncat", "strchr", "strrchr", "strcmp", "strncmp",
    "strcpy", "strncpy", "strerror", "strlen", "strpbrk", "strspn",
    "strcspn", "strstr", "strtok"
  };
  ADD_TO_SYSTEM_LIBRARY(string_syms, "string.h");

  // time.h
  const char* time_syms[]={
    "asctime", "asctime_r", "ctime", "ctime_r", "difftime", "gmtime",
    "gmtime_r", "localtime", "localtime_r", "mktime",
    /* non-public struct types */
    "tag-timespec", "tag-timeval"
  };
  ADD_TO_SYSTEM_LIBRARY(time_syms, "time.h");

  // unistd.h
  const char* unistd_syms[]={
    "_exit", "access", "alarm", "chdir", "chown", "close", "dup",
    "dup2", "execl", "execle", "execlp", "execv", "execve", "execvp",
    "fork", "fpathconf", "getcwd", "getegid", "geteuid", "getgid",
    "getgroups", "getlogin", "getpgrp", "getpid", "getppid", "getuid",
    "isatty", "link", "lseek", "pathconf", "pause", "pipe", "read",
    "rmdir", "setgid", "setpgid", "setsid", "setuid", "sleep",
    "sysconf", "tcgetpgrp", "tcsetpgrp", "ttyname", "ttyname_r",
    "unlink", "write"
  };
  ADD_TO_SYSTEM_LIBRARY(unistd_syms, "unistd.h");

  // sys/select.h
  const char* sys_select_syms[]={
    "select"
  };
  ADD_TO_SYSTEM_LIBRARY(sys_select_syms, "sys/select.h");

  // sys/socket.h
  const char* sys_socket_syms[]={
    "accept", "bind", "connect"
  };
  ADD_TO_SYSTEM_LIBRARY(sys_socket_syms, "sys/socket.h");

  // sys/stat.h
  const char* sys_stat_syms[]={
    "fstat", "lstat", "stat"
  };
  ADD_TO_SYSTEM_LIBRARY(sys_stat_syms, "sys/stat.h");

  /*
  // sys/types.h
  const char* sys_types_syms[]={
  };
  ADD_TO_SYSTEM_LIBRARY(sys_types_syms, "sys/types.h");
  */

  // sys/wait.h
  const char* sys_wait_syms[]={
    "wait", "waitpid"
  };
  ADD_TO_SYSTEM_LIBRARY(sys_wait_syms, "sys/wait.h");
}

/*******************************************************************\

Function: dump_ct::ignore

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool dump_ct::ignore(const symbolt &symbol)
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

  const std::string &file_str=id2string(symbol.location.get_file());

  // don't dump internal GCC builtins
  if((file_str=="gcc_builtin_headers_alpha.h" ||
      file_str=="gcc_builtin_headers_arm.h" ||
      file_str=="gcc_builtin_headers_ia32.h" ||
      file_str=="gcc_builtin_headers_mips.h" ||
      file_str=="gcc_builtin_headers_power.h" ||
      file_str=="gcc_builtin_headers_generic.h") &&
     has_prefix(name_str, "__builtin_"))
    return true;

  if(name_str=="__builtin_va_start" ||
     name_str=="__builtin_va_end" ||
     symbol.name==ID_gcc_builtin_va_arg)
  {
    system_headers.insert("stdarg.h");
    return true;
  }

  if(name_str.find("$link")!=std::string::npos)
    return false;

  system_library_mapt::const_iterator it=
    system_library_map.find(symbol.name);

  if(it!=system_library_map.end())
  {
    system_headers.insert(it->second);
    return true;
  }

  return false;
}

/*******************************************************************\

Function: dump_ct::cleanup_decl

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::cleanup_decl(
  code_declt &decl,
  std::list<irep_idt> &local_static,
  std::list<irep_idt> &local_type_decls)
{
  exprt value=nil_exprt();

  if(decl.operands().size()==2)
  {
    value=decl.op1();
    decl.operands().resize(1);
  }

  goto_programt tmp;
  goto_programt::targett t=tmp.add_instruction(DECL);
  t->code=decl;

  if(value.is_not_nil())
  {
    t=tmp.add_instruction(ASSIGN);
    t->code=code_assignt(decl.op0(), value);
  }

  tmp.add_instruction(END_FUNCTION);

  code_blockt b;
  goto_program2codet p2s(
    irep_idt(),
    tmp,
    copied_symbol_table,
    b,
    local_static,
    local_type_decls,
    system_headers);
  p2s();

  assert(b.operands().size()==1);
  decl.swap(b.op0());
}

/*******************************************************************\

Function: dump_ct::convert_global_variables

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::convert_global_variable(
    const symbolt &symbol,
    std::ostream &os,
    local_static_declst &local_static_decls)
{
  const irep_idt &func=symbol.location.get_function();
  if((func.empty() || symbol.is_extern || symbol.value.is_not_nil()) &&
      !converted.insert(symbol.name).second)
    return;

  code_declt d(symbol.symbol_expr());

  find_symbols_sett syms;
  if(symbol.value.is_not_nil())
    find_symbols(symbol.value, syms);

  // add a tentative declaration to cater for symbols in the initializer
  // relying on it this symbol
  if((func.empty() || symbol.is_extern) &&
     (symbol.value.is_nil() || !syms.empty()))
  {
    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location << std::endl;
    os << expr_to_string(d) << std::endl;
  }

  if(!symbol.value.is_nil())
  {
    std::set<std::string> symbols_sorted;
    for(find_symbols_sett::const_iterator
        it=syms.begin();
        it!=syms.end();
        ++it)
      if(!symbols_sorted.insert(id2string(*it)).second)
        assert(false);

    for(std::set<std::string>::const_iterator
        it=symbols_sorted.begin();
        it!=symbols_sorted.end();
        ++it)
    {
      const symbolt &sym=ns.lookup(*it);
      if(!sym.is_type && sym.is_static_lifetime && sym.type.id()!=ID_code)
        convert_global_variable(sym, os, local_static_decls);
    }

    d.copy_to_operands(symbol.value);
  }

  if(!func.empty() && !symbol.is_extern)
    local_static_decls[symbol.name]=d;
  else if(!symbol.value.is_nil())
  {
    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location << std::endl;

    std::list<irep_idt> empty_static, empty_types;
    cleanup_decl(d, empty_static, empty_types);
    assert(empty_static.empty());
    os << expr_to_string(d) << std::endl;
  }
}

/*******************************************************************\

Function: dump_ct::convert_function_declarations

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::convert_function_declaration(
    const symbolt& symbol,
    const bool skip_main,
    std::ostream &os_decl,
    std::ostream &os_body,
    local_static_declst &local_static_decls)
{
  // don't dump artificial main
  if(skip_main && symbol.name==goto_functionst::entry_point())
    return;

  // convert the goto program back to code - this might change
  // the function type
  goto_functionst::function_mapt::const_iterator func_entry=
    goto_functions.function_map.find(symbol.name);
  if(func_entry!=goto_functions.function_map.end() &&
     func_entry->second.body_available)
  {
    code_blockt b;
    std::list<irep_idt> type_decls, local_static;

    goto_program2codet p2s(
      symbol.name,
      func_entry->second.body,
      copied_symbol_table,
      b,
      local_static,
      type_decls,
      system_headers);
    p2s();

    insert_local_static_decls(
      b,
      local_static,
      local_static_decls,
      type_decls);

    convertedt converted_bak(converted);
    insert_local_type_decls(
      b,
      type_decls);
    converted.swap(converted_bak);

    os_body << "// " << symbol.name << std::endl;
    os_body << "// " << symbol.location << std::endl;
    os_body << make_decl(symbol.name, symbol.type) << std::endl;
    os_body << expr_to_string(b);
    os_body << std::endl << std::endl;
  }

  if(symbol.name!=goto_functionst::entry_point() &&
     symbol.name!=ID_main)
  {
    os_decl << "// " << symbol.name << std::endl;
    os_decl << "// " << symbol.location << std::endl;
    os_decl << make_decl(symbol.name, symbol.type) << ";" << std::endl;
  }
}

/*******************************************************************\

Function: find_block_position_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

static bool find_block_position_rec(
  const irep_idt &identifier,
  codet &root,
  code_blockt* &dest,
  exprt::operandst::iterator &before)
{
  if(!root.has_operands())
    return false;

  code_blockt* our_dest=0;

  exprt::operandst &operands=root.operands();
  exprt::operandst::iterator first_found=operands.end();

  Forall_expr(it, operands)
  {
    bool found=false;

    // be aware of the skip-carries-type hack
    if(it->id()==ID_code &&
       to_code(*it).get_statement()!=ID_skip)
      found=find_block_position_rec(
        identifier,
        to_code(*it),
        our_dest,
        before);
    else
    {
      find_symbols_sett syms;
      find_type_and_expr_symbols(*it, syms);

      found=syms.find(identifier)!=syms.end();
    }

    if(!found) continue;

    if(!our_dest)
    {
      // first containing block
      if(root.get_statement()==ID_block)
      {
        dest=&(to_code_block(root));
        before=it;
      }

      return true;
    }
    else
    {
      // there is a containing block and this is the first operand
      // that contains identifier
      if(first_found==operands.end())
        first_found=it;
      // we have seen it already - pick the first occurrence in this
      // block
      else if(root.get_statement()==ID_block)
      {
        dest=&(to_code_block(root));
        before=first_found;

        return true;
      }
      // we have seen it already - outer block has to deal with this
      else
        return true;
    }
  }

  if(first_found!=operands.end())
  {
    dest=our_dest;

    return true;
  }

  return false;
}

/*******************************************************************\

Function: dump_ct::insert_local_static_decls

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::insert_local_static_decls(
  code_blockt &b,
  const std::list<irep_idt> &local_static,
  local_static_declst &local_static_decls,
  std::list<irep_idt> &type_decls)
{
  // look up last identifier first as its value may introduce the
  // other ones
  for(std::list<irep_idt>::const_reverse_iterator
      it=local_static.rbegin();
      it!=local_static.rend();
      ++it)
  {
    local_static_declst::const_iterator d_it=
      local_static_decls.find(*it);
    assert(d_it!=local_static_decls.end());

    code_declt d=d_it->second;
    std::list<irep_idt> redundant;
    cleanup_decl(d, redundant, type_decls);

    code_blockt* dest_ptr=0;
    exprt::operandst::iterator before=b.operands().end();

    // some use of static variables might be optimised out if it is
    // within an if(false) { ... } block
    if(find_block_position_rec(*it, b, dest_ptr, before))
    {
      assert(dest_ptr!=0);
      dest_ptr->operands().insert(before, d);
    }
  }
}

/*******************************************************************\

Function: dump_ct::insert_local_type_decls

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::insert_local_type_decls(
  code_blockt &b,
  const std::list<irep_idt> &type_decls)
{
  // look up last identifier first as its value may introduce the
  // other ones
  for(std::list<irep_idt>::const_reverse_iterator
      it=type_decls.rbegin();
      it!=type_decls.rend();
      ++it)
  {
    const typet &type=ns.lookup(*it).type;
    // feed through plain C to expr2c by ending and re-starting
    // a comment block ...
    std::ostringstream os_body;
    os_body << *it << " */\n";
    convert_compound(type, false, os_body);
    os_body << "/*";

    code_skipt skip;
    skip.add_source_location().set_comment(os_body.str());
    // another hack to ensure symbols inside types are seen
    skip.type()=type;

    code_blockt* dest_ptr=0;
    exprt::operandst::iterator before=b.operands().end();

    // we might not find it in case a transparent union type cast
    // has been removed by cleanup operations
    if(find_block_position_rec(*it, b, dest_ptr, before))
    {
      assert(dest_ptr!=0);
      dest_ptr->operands().insert(before, skip);
    }
  }
}

/*******************************************************************\

Function: dump_ct::cleanup_expr

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::cleanup_expr(exprt &expr)
{
  Forall_operands(it, expr)
    cleanup_expr(*it);

  cleanup_type(expr.type());

  if(expr.id()==ID_struct)
  {
    struct_typet type=
      to_struct_type(ns.follow(expr.type()));

    struct_union_typet::componentst old_components;
    old_components.swap(type.components());

    exprt::operandst old_ops;
    old_ops.swap(expr.operands());

    assert(old_components.size()==old_ops.size());
    exprt::operandst::iterator o_it=old_ops.begin();
    for(struct_union_typet::componentst::const_iterator
        it=old_components.begin();
        it!=old_components.end();
        ++it)
    {
      const bool is_zero_bit_field=
        it->type().id()==ID_c_bit_field &&
        to_c_bit_field_type(it->type()).get_width()==0;

      if(!it->get_is_padding() && !is_zero_bit_field)
      {
        type.components().push_back(*it);
        expr.move_to_operands(*o_it);
      }
      ++o_it;
    }
    expr.type().swap(type);
  }
  else if(expr.id()==ID_union &&
          (expr.type().get_bool(ID_C_transparent_union) ||
           ns.follow(expr.type()).get_bool(ID_C_transparent_union)))
  {
    union_exprt &u=to_union_expr(expr);

    // add a typecast for NULL
    if(u.op().id()==ID_constant &&
       u.op().type().id()==ID_pointer &&
       u.op().type().subtype().id()==ID_empty &&
       (u.op().is_zero() || to_constant_expr(u.op()).get_value()==ID_NULL))
    {
      const struct_union_typet::componentt &comp=
        to_union_type(ns.follow(u.type())).get_component(u.get_component_name());
      const typet &u_op_type=comp.type();
      assert(u_op_type.id()==ID_pointer);

      typecast_exprt tc(u.op(), u_op_type);
      expr.swap(tc);
    }
    else
    {
      exprt tmp;
      tmp.swap(u.op());
      expr.swap(tmp);
    }
  }
  else if(expr.id()==ID_typecast &&
      expr.op0().id()==ID_typecast &&
      base_type_eq(expr.type(), expr.op0().type(), ns))
  {
    exprt tmp=expr.op0();
    expr.swap(tmp);
  }
  else if(expr.id()==ID_code &&
          to_code(expr).get_statement()==ID_function_call &&
          to_code_function_call(to_code(expr)).function().id()==ID_symbol)
  {
    code_function_callt &call=to_code_function_call(to_code(expr));
    const symbol_exprt &fn=to_symbol_expr(call.function());
    code_function_callt::argumentst &arguments=call.arguments();

    // don't edit function calls we might have introduced
    const symbolt *s;
    if(!ns.lookup(fn.get_identifier(), s))
    {
      const symbolt &fn_sym=ns.lookup(fn.get_identifier());
      const code_typet &code_type=to_code_type(fn_sym.type);
      const code_typet::parameterst &parameters=code_type.parameters();

      if(parameters.size()==arguments.size())
      {
        code_typet::parameterst::const_iterator it=parameters.begin();
        Forall_expr(it2, arguments)
        {
          const typet &type=ns.follow(it->type());
          if(type.id()==ID_union &&
             type.get_bool(ID_C_transparent_union))
          {
            if(it2->id()==ID_typecast &&
               base_type_eq(it2->type(), type, ns))
              *it2=to_typecast_expr(*it2).op();

            // add a typecast for NULL or 0
            if(it2->id()==ID_constant &&
               (it2->is_zero() || to_constant_expr(*it2).get_value()==ID_NULL))
            {
              const typet &comp_type=
                to_union_type(type).components().front().type();

              if(comp_type.id()==ID_pointer)
                *it2=typecast_exprt(*it2, comp_type);
            }
          }

          ++it;
        }
      }
    }
  }
  else if(expr.id()==ID_constant &&
          expr.type().id()==ID_signedbv)
  {
    const irep_idt &cformat=expr.get(ID_C_cformat);

    if(!cformat.empty() &&
       declared_enum_constants.find(cformat)==
       declared_enum_constants.end() &&
       !std::isdigit(id2string(cformat)[0]))
      expr.remove(ID_C_cformat);
  }
}

/*******************************************************************\

Function: dump_ct::cleanup_type

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::cleanup_type(typet &type)
{
  Forall_subtypes(it, type)
    cleanup_type(*it);

  if(type.id()==ID_array)
    cleanup_expr(to_array_type(type).size());

  assert((type.id()!=ID_union && type.id()!=ID_struct) ||
         !type.get(ID_tag).empty());
}

/*******************************************************************\

Function: dump_ct::type_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string dump_ct::type_to_string(const typet &type)
{
  std::string ret;
  typet t=type;
  cleanup_type(t);
  language->from_type(t, ret, ns);
  return ret;
}

/*******************************************************************\

Function: dump_ct::expr_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string dump_ct::expr_to_string(const exprt &expr)
{
  std::string ret;
  exprt e=expr;
  cleanup_expr(e);
  language->from_expr(e, ret, ns);
  return ret;
}

/*******************************************************************\

Function: dump_c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_c(
  const goto_functionst &src,
  const bool use_system_headers,
  const namespacet &ns,
  std::ostream &out)
{
  dump_ct goto2c(src, use_system_headers, ns, new_ansi_c_language);
  out << goto2c;
}

/*******************************************************************\

Function: dump_cpp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_cpp(
  const goto_functionst &src,
  const bool use_system_headers,
  const namespacet &ns,
  std::ostream &out)
{
  dump_ct goto2cpp(src, use_system_headers, ns, new_cpp_language);
  out << goto2cpp;
}

