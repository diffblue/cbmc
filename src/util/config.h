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
    std::size_t int_width;
    std::size_t long_int_width;
    std::size_t bool_width;
    std::size_t char_width;
    std::size_t short_int_width;
    std::size_t long_long_int_width;
    std::size_t pointer_width;
    std::size_t single_width;
    std::size_t double_width;
    std::size_t long_double_width;
    std::size_t wchar_t_width;

    // various language options
    bool char_is_unsigned, wchar_t_is_unsigned;
    bool for_has_scope;
    bool ts_18661_3_Floatn_types; // ISO/IEC TS 18661-3:2015
    bool Float128_type;
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
    std::size_t alignment;

    // maximum minimum size of the operands for a machine
    // instruction (in bytes)
    std::size_t memory_operand_size;

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
    void set_arch_spec_riscv64();
    void set_arch_spec_s390();
    void set_arch_spec_s390x();
    void set_arch_spec_sparc(const irep_idt &subarch);
    void set_arch_spec_ia64();
    void set_arch_spec_x32();
    void set_arch_spec_v850();
    void set_arch_spec_hppa();
    void set_arch_spec_sh4();

    enum class flavourt
    {
      NONE,
      ANSI,
      GCC,
      ARM,
      CLANG,
      VISUAL_STUDIO,
      CODEWARRIOR
    };
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

    static const std::size_t default_object_bits=8;
  } ansi_c;

  struct cppt
  {
    enum class cpp_standardt { CPP98, CPP03, CPP11, CPP14 } cpp_standard;
    static cpp_standardt default_cpp_standard();

    void set_cpp98() { cpp_standard=cpp_standardt::CPP98; }
    void set_cpp03() { cpp_standard=cpp_standardt::CPP03; }
    void set_cpp11() { cpp_standard=cpp_standardt::CPP11; }
    void set_cpp14() { cpp_standard=cpp_standardt::CPP14; }

    static const std::size_t default_object_bits=8;
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

    static const std::size_t default_object_bits=16;
  } java;

  struct bv_encodingt
  {
    // number of bits to encode heap object addresses
    std::size_t object_bits;
    bool is_object_bits_default;

    static const std::size_t default_object_bits=8;
  } bv_encoding;

  // this is the function to start executing
  std::string main;

  void set_arch(const irep_idt &);

  void set_from_symbol_table(const symbol_tablet &);

  bool set(const cmdlinet &cmdline);

  void set_object_bits_from_symbol_table(const symbol_tablet &);
  std::string object_bits_info();

  static irep_idt this_architecture();
  static irep_idt this_operating_system();

private:
  void set_classpath(const std::string &cp);
};

extern configt config;

#endif // CPROVER_UTIL_CONFIG_H
