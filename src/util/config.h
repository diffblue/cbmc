/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_CONFIG_H
#define CPROVER_UTIL_CONFIG_H

#include "cmdline.h"
#include "ieee_float.h"

class configt
{
public:
  struct ansi_ct
  {
    // for ANSI-C
    unsigned int_width;
    unsigned long_int_width;
    unsigned char_width;
    unsigned short_int_width;
    unsigned long_long_int_width;
    unsigned pointer_width;
    unsigned single_width;
    unsigned double_width;
    unsigned long_double_width;
    unsigned wchar_t_width;
    
    bool char_is_unsigned;
    bool use_fixed_for_float;
    
    ieee_floatt::rounding_modet rounding_mode;

    void set_16();
    void set_32();
    void set_64();

    // http://www.unix.org/version2/whatsnew/lp64_wp.html
    void set_LP64();  // int=32, long=64, pointer=64
    void set_ILP64(); // int=64, long=64, pointer=64
    void set_LLP64(); // int=32, long=32, pointer=64
    void set_ILP32(); // int=32, long=32, pointer=32
    void set_LP32();  // int=16, long=32, pointer=32

    void set_from_context(const class contextt &context);
    
    // minimum alignment (in structs) measured in bytes
    unsigned alignment;
    
    typedef enum { NO_ENDIANESS, IS_LITTLE_ENDIAN, IS_BIG_ENDIAN } endianesst;
    endianesst endianess;

    typedef enum { NO_OS, OS_LINUX, OS_MACOS, OS_WIN } ost;
    ost os;

    typedef enum { NO_ARCH, ARCH_I386, ARCH_PPC, ARCH_X86_64 } archt;
    archt arch;
    
    typedef enum { NO_MODE, MODE_ANSI, MODE_GCC, MODE_VISUAL_STUDIO,
                   MODE_CODEWARRIOR, MODE_ARM } modet;
    modet mode;

    std::list<std::string> defines;
    std::list<std::string> undefines;
    std::list<std::string> preprocessor_options;
    std::list<std::string> include_paths;
    std::list<std::string> include_files;

    typedef enum { LIB_NONE, LIB_FULL } libt;
    libt lib;
    bool string_abstraction;
    
  protected:
    int from_ns(const class namespacet &ns, const std::string &what);
  } ansi_c;
  
  struct verilogt
  {
    std::list<std::string> include_paths;
  } verilog;

  // this is the function to start executing
  std::string main;
  
  bool set(const cmdlinet &cmdline);
};

extern configt config;

#endif
