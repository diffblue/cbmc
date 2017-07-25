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
    enum class c_standardt { C89, C99, C11 } c_standard;
    static c_standardt default_c_standard();

    void set_c89() { c_standard=c_standardt::C89; for_has_scope=false; }
    void set_c99() { c_standard=c_standardt::C99; for_has_scope=true; }
    void set_c11() { c_standard=c_standardt::C11; for_has_scope=true; }

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

    // minimum alignment (in structs) measured in bytes
    unsigned alignment;

    // maximum minimum size of the operands for a machine
    // instruction (in bytes)
    unsigned memory_operand_size;

    enum class endiannesst { NO_ENDIANNESS, IS_LITTLE_ENDIAN, IS_BIG_ENDIAN };
    endiannesst endianness;

    enum class ost { NO_OS, OS_LINUX, OS_MACOS, OS_WIN };
    ost os;

    static std::string os_to_string(ost);
    static ost string_to_os(const std::string &);

    irep_idt arch;

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
    void set_arch_spec_v850();
    void set_arch_spec_hppa();
    void set_arch_spec_sh4();

    enum class flavourt { NONE, ANSI, GCC, ARM, APPLE,
                          VISUAL_STUDIO, CODEWARRIOR };
    flavourt mode; // the syntax of source files

    enum class preprocessort { NONE, GCC, CLANG, VISUAL_STUDIO,
                               CODEWARRIOR, ARM };
    preprocessort preprocessor; // the preprocessor to use

    std::list<std::string> defines;
    std::list<std::string> undefines;
    std::list<std::string> preprocessor_options;
    std::list<std::string> include_paths;
    std::list<std::string> include_files;

    enum class libt { LIB_NONE, LIB_FULL };
    libt lib;

    bool string_abstraction;
  } ansi_c;

  struct cppt
  {
    enum class cpp_standardt { CPP98, CPP03, CPP11, CPP14 } cpp_standard;
    static cpp_standardt default_cpp_standard();

    void set_cpp98() { cpp_standard=cpp_standardt::CPP98; }
    void set_cpp03() { cpp_standard=cpp_standardt::CPP03; }
    void set_cpp11() { cpp_standard=cpp_standardt::CPP11; }
    void set_cpp14() { cpp_standard=cpp_standardt::CPP14; }
  } cpp;

  struct verilogt
  {
    std::list<std::string> include_paths;
  } verilog;

  struct javat
  {
    typedef std::list<std::string> classpatht;
    classpatht classpath;
    irep_idt main_class;
  } java;

  // this is the function to start executing
  std::string main;

  void set_arch(const irep_idt &);

  void set_from_symbol_table(const symbol_tablet &);

  bool set(const cmdlinet &cmdline);

  static irep_idt this_architecture();
  static irep_idt this_operating_system();

private:
  void set_classpath(const std::string &cp);
};

extern configt config;

#endif // CPROVER_UTIL_CONFIG_H
