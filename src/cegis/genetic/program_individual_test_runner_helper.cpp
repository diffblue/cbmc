/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/substitute.h>

#include <cegis/instrument/literals.h>
#include <cegis/genetic/program_individual_test_runner_helper.h>

void implement_program_individual_deserialise(std::string &source,
    const bool danger)
{
  source+=
      "#include <string.h>\n\n"
          "#define " CEGIS_PREFIX "next_arg() argv[" CEGIS_PREFIX "deserialise_index++]\n";
  source+=
      danger ?
          "#define " CEGIS_PREFIX "deserialise_init() unsigned int " CEGIS_PREFIX "deserialise_index=" CEGIS_PREFIX "first_prog_offset\n" :
          "#define " CEGIS_PREFIX "deserialise_init() unsigned int " CEGIS_PREFIX "deserialise_index=0u\n";
  source+=
      "#define " CEGIS_PREFIX "declare_prog(var_name, sz) const size_t sz=" CEGIS_PREFIX "next_arg(); \\\n"
      "  struct " CEGIS_PREFIX "instructiont var_name[sz]; \\\n"
      "for (unsigned int i=0; i < sizeof(var_name) / sizeof(struct " CEGIS_PREFIX "instructiont); ++i) \\\n"
      "{ \\\n"
      "  var_name[i].opcode=" CEGIS_PREFIX "next_arg(); \\\n"
      "  var_name[i].op0=" CEGIS_PREFIX "next_arg(); \\\n"
      "  var_name[i].op1=" CEGIS_PREFIX "next_arg(); \\\n"
      "  var_name[i].op2=" CEGIS_PREFIX "next_arg(); \\\n"
      "}\n"
      "#define " CEGIS_PREFIX "deserialise_x0(var_name) var_name=" CEGIS_PREFIX "next_arg()\n";
  source+=
      danger ?
          "#define " CEGIS_PREFIX "ce_value_init() unsigned int " CEGIS_PREFIX "ce_index=0u\n" :
          "#define " CEGIS_PREFIX "ce_value_init() unsigned int " CEGIS_PREFIX "ce_index=" CEGIS_PREFIX "deserialise_index\n";
  source+=
      "#define " CEGIS_PREFIX "ce_value() argv[" CEGIS_PREFIX "ce_index++]\n";

}

namespace
{
void add_default_return(std::string &source)
{
  source.replace(source.rfind('}'), 1, "return 0;}");
}
}

void transform_program_individual_main_to_lib(std::string &source,
    const bool danger)
{
  substitute(source, "int main(const int argc, const char * const argv[])\n"
      "{\n", "int " CEGIS_FITNESS_TEST_FUNC "(const unsigned int argv[])\n"
  "{\n"
  "memset(" CEGIS_OPS ", 0, sizeof(" CEGIS_OPS "));\n"
  "memset(" CEGIS_RESULT_OPS ", 0, sizeof(" CEGIS_RESULT_OPS "));\n");
  add_default_return(source);
}
