/*******************************************************************\

Module: RRA Specification-Based Generation

Author: Adrian Palacios accorell@amazon.com
        Murali Talupur  talupur@amazon.com
        Lefan Zhang     lefanz@amazon.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_RRA_SPEC_GEN_H
#define CPROVER_GOTO_INSTRUMENT_RRA_SPEC_GEN_H

class rra_spec_gent
{
private:
  static size_t count_concs(std::string shape_type);

  static void generate_fun_abs(
    size_t spec_index,
    std::string shape_type,
    std::ostream &output);

  static void generate_fun_conc(
    size_t spec_index,
    std::string shape_type,
    std::ostream &output);

  static void generate_fun_prec(
    size_t spec_index,
    std::string shape_type,
    std::ostream &output);

  static void generate_fun_add(
    size_t spec_index,
    std::string shape_type,
    std::ostream &output);

  static void generate_fun_sub(
    size_t spec_index,
    std::string shape_type,
    std::ostream &output);

  static void generate_fun_mult(
    size_t spec_index,
    std::string shape_type,
    std::ostream &output);

public:
  static void generate_abst_funcs_hdr(std::ostream &output);

  static std::vector<irep_idt> generate_indices(std::string shape_type);

  static std::vector<std::string>
  generate_assumptions(std::string shape_type, std::vector<irep_idt> indices);

  static void generate_functions(
    size_t spec_index,
    std::string shape_type,
    std::ostream &output);
};

#endif // CPROVER_GOTO_INSTRUMENT_RRA_SPEC_GEN_H
