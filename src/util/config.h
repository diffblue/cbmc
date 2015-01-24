/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_CONFIG_H
#define CPROVER_UTIL_CONFIG_H

#include <list>

#include "ieee_float.h"
#include "irep.h"

class cmdlinet;
class symbol_tablet;
class namespacet;

/*! \brief Globally accessible architectural configuration
*/
class configt
{
public:
  struct ansi_ct
  {
    // for ANSI-C
    unsigned int_width;
    unsigned long_int_width;
    unsigned bool_width;
    unsigned char_width;
    unsigned short_int_width;
    unsigned long_long_int_width;
    unsigned pointer_width;
    unsigned single_width;
    unsigned double_width;
    unsigned long_double_width;
    unsigned wchar_t_width;
    
    // various language options
    bool char_is_unsigned, wchar_t_is_unsigned;
    bool use_fixed_for_float;
    bool for_has_scope;
    bool single_precision_constant;
    bool cpp11;
    
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

    void set_from_symbol_table(const symbol_tablet &symbol_table);
    
    // minimum alignment (in structs) measured in bytes
    unsigned alignment;

    // maximum minimum size of the operands for a machine 
    // instruction (in bytes)
    unsigned memory_operand_size;
    
    typedef enum { NO_ENDIANNESS, IS_LITTLE_ENDIAN, IS_BIG_ENDIAN } endiannesst;
    endiannesst endianness;

    typedef enum { NO_OS, OS_LINUX, OS_MACOS, OS_WIN } ost;
    ost os;

    typedef enum { NO_ARCH, ARCH_I386, ARCH_X86_64, ARCH_POWER, ARCH_ARM,
                   ARCH_ALPHA, ARCH_MIPS, ARCH_S390, ARCH_S390X, ARCH_SPARC,
                   ARCH_IA64, ARCH_X32 } archt;
    archt arch;

    // architecture-specific integer value of null pointer constant
    bool NULL_is_zero;

    void set_arch_spec_i386();
    void set_arch_spec_x86_64();
    void set_arch_spec_power(const irep_idt &subarch);
    void set_arch_spec_arm(const irep_idt &subarch);
    void set_arch_spec_alpha();
    void set_arch_spec_mips(const irep_idt &subarch);
    void set_arch_spec_s390();
    void set_arch_spec_s390x();
    void set_arch_spec_sparc(const irep_idt &subarch);
    void set_arch_spec_ia64();
    void set_arch_spec_x32();
    
    typedef enum { NO_MODE, MODE_ANSI_C_CPP, MODE_GCC_C, MODE_GCC_CPP,
                   MODE_VISUAL_STUDIO_C_CPP,
                   MODE_CODEWARRIOR_C_CPP, MODE_ARM_C_CPP } flavourt;
    flavourt mode; // the syntax of source files

    typedef enum { NO_PP, PP_GCC, PP_CLANG, PP_VISUAL_STUDIO,
                   PP_CODEWARRIOR, PP_ARM } preprocessort;
    preprocessort preprocessor; // the preprocessor to use

    std::list<std::string> defines;
    std::list<std::string> undefines;
    std::list<std::string> preprocessor_options;
    std::list<std::string> include_paths;
    std::list<std::string> include_files;

    typedef enum { LIB_NONE, LIB_FULL } libt;
    libt lib;
    bool string_abstraction;
  } ansi_c;
  
  struct verilogt
  {
    std::list<std::string> include_paths;
  } verilog;

  // this is the function to start executing
  std::string main;
  
  bool set(const cmdlinet &cmdline);
  
  static irep_idt this_architecture();
  static irep_idt this_operating_system();
};

extern configt config;

#endif
