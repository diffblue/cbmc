/*******************************************************************\

Module: RRA Specification-Based Generation

Author: Adrian Palacios accorell@amazon.com
        Murali Talupur  talupur@amazon.com
        Lefan Zhang     lefanz@amazon.com

\*******************************************************************/

#include <util/cprover_prefix.h>
#include <util/irep.h>

#include <string>
#include <vector>

#include "rra_spec_gen.h"

std::vector<irep_idt> rra_spec_gent::generate_indices(std::string shape_type)
{
  std::vector<irep_idt> indices;
  size_t num_concs = count_concs(shape_type);

  for(size_t i = 0; i < num_concs; i++)
  {
    irep_idt index;
    index = "cncrt" + std::to_string(i);
    indices.push_back(index);
  }

  return indices;
}

/*
 * Generate a set of assumptions given a shape and a set of indices
 *
 * If the first symbol is a 'c', we must add assumption "cncrt0==0".
 * In the general case, whenever we find a 'c' ("cncrtX") in the shape,
 * we add an assumption depending on the preceding symbol:
 *  - 'c': "cncrtY==cncrtX-1"
 *  - '*': "cncrtY<cncrtX"
 * where Y = X-1
 *
 * Example: c*c*c*
 * Output: ["cncrt0==0","cncrt0<cncrt1","cncrt1<cncrt2"]
 *
 * Example: *cc*c*
 * Output: ["cncrt0==cncrt1-1","cncrt1<cncrt2"]
 */
std::vector<std::string> rra_spec_gent::generate_assumptions(
  std::string shape_type,
  std::vector<irep_idt> indices)
{
  std::vector<std::string> assumptions;
  size_t shape_len = shape_type.length();
  size_t cur_c = 0;

  if(shape_type[0] == 'c')
  {
    std::string fst_assumption = id2string(indices[0]) + "==0";
    assumptions.push_back(fst_assumption);
  }

  for(size_t i = 0; i < shape_len; i++)
  {
    if(shape_type[i] == 'c' || shape_type[i] == 'l')
    {
      if(cur_c > 0)
      {
        std::string assumption;

        if(shape_type[i - 1] == '*')
        {
          assumption =
            id2string(indices[cur_c - 1]) + "<" + id2string(indices[cur_c]);
        }
        else // shape_type[i - 1] == 'c'
        {
          assumption = id2string(indices[cur_c - 1]) +
                       "==" + id2string(indices[cur_c]) + "-1";
        }

        assumptions.push_back(assumption);
      }
      cur_c++;
    }
  }

  return assumptions;
}

void rra_spec_gent::generate_functions(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  generate_fun_abs(spec_index, shape_type, output);
  generate_fun_conc(spec_index, shape_type, output);
  generate_fun_prec(spec_index, shape_type, output);
  generate_fun_add(spec_index, shape_type, output);
  generate_fun_sub(spec_index, shape_type, output);
  generate_fun_mult(spec_index, shape_type, output);
}

size_t rra_spec_gent::count_concs(std::string shape_type)
{
  size_t num_concs = 0;
  size_t shape_len = shape_type.length();

  for(size_t i = 0; i < shape_len; i++)
    if(shape_type[i] == 'c' || shape_type[i] == 'l')
      num_concs++;

  return num_concs;
}

void rra_spec_gent::generate_abst_funcs_hdr(std::ostream &output)
{
  output << "#include <stdint.h>\n";
  output << "#include <assert.h>\n";
  output << "#include <stddef.h>\n";
  output << "#include <stdbool.h>\n\n";

  output << "size_t nndt_int(){\n";
  output << "\tsize_t i;\n";
  output << "\treturn(i);\n";
  output << "}\n\n";

  output << "bool nndt_bool(){\n";
  output << "\tsize_t i;\n";
  output << "\treturn(i % 2);\n";
  output << "}\n\n";

  output << "size_t nndt_under(size_t bound){\n";
  output << "\tsize_t nd;\n";
  output << "\t" CPROVER_PREFIX "assume(nd < bound);\n";
  output << "\treturn(nd);\n";
  output << "}\n\n";

  output << "size_t nndt_between(size_t l, size_t u){\n";
  output << "\tsize_t diff = u - l;\n";
  output << "\tsize_t nd = nndt_under(diff);\n";
  output << "\tif (nd == 0) return(l+1);\n";
  output << "\telse return(nd + l);\n";
  output << "}\n\n";

  output << "size_t nndt_above(size_t bound){\n";
  output << "\tsize_t nd = nndt_int();\n";
  output << "\t" CPROVER_PREFIX "assume(nd < bound);\n";
  output << "\treturn(nd);\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_abs(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  size_t num_concs = count_concs(shape_type);
  size_t cur_idx = 0;
  size_t cur_c = 1;
  size_t shape_len = shape_type.length();
  size_t last_i = shape_len - 1;

  output << "// Detected shape: " + shape_type + "\n";
  output << "size_t abs_" + std::to_string(spec_index) + "(size_t index,";

  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "size_t a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ") {\n";

  // first type is best handled separately
  if(shape_type[0] == '*')
  {
    output << "\tif (index < a" + std::to_string(cur_c) + ") return " +
                std::to_string(cur_idx) + ";\n";
    cur_idx++;
  }
  else // shape_type[0] == 'c' || shape_type[0] == 'l'
  {
    output << "\tif (index == a" + std::to_string(cur_c) + ") return " +
                std::to_string(cur_idx) + ";\n";
    cur_idx++;
    cur_c++;
  }

  // general algorithm for [1..n-1] types
  for(size_t i = cur_idx; i < last_i; i++)
  {
    if(shape_type[i] == '*')
    {
      output << "\tif (index > a" + std::to_string(cur_c - 1) +
                  " && index < a" + std::to_string(cur_c) + ") return " +
                  std::to_string(cur_idx) + ";\n";
      cur_idx++;
    }
    else // shape_type[i] == 'c' || shape_type[i] == 'l'
    {
      output << "\tif (index == a" + std::to_string(cur_c) + ") return " +
                  std::to_string(cur_idx) + ";\n";
      cur_c++;
      cur_idx++;
    }
  }

  if(shape_type[last_i] == '*')
  {
    output << "\tif (index > a" + std::to_string(cur_c - 1) + ") return " +
                std::to_string(cur_idx) + ";\n";
  }
  else // shape_type[last_i] == 'c' || shape_type[last_i] == 'l'
  {
    output << "\tif (index == a" + std::to_string(cur_c) + ") return " +
                std::to_string(cur_idx) + ";\n";
  }
  output << "\tassert(0!=0);\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_conc(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  size_t num_concs = count_concs(shape_type);
  size_t cur_idx = 0;
  size_t cur_c = 1;
  size_t shape_len = shape_type.length();
  size_t last_i = shape_len - 1;

  output << "size_t conc_" + std::to_string(spec_index) + "(size_t abs_ind,";

  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "size_t a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ") {\n";
  output << "\tassert(abs_ind >= 0);\n";
  output << "\tassert(a1 >= 0);\n";

  for(size_t i = 1; i < num_concs; i++)
  {
    output << "\tassert(a" + std::to_string(i) + " < a" +
                std::to_string(i + 1) + ");\n";
  }
  output << "\n";

  if(shape_type[0] == '*')
  {
    output << "\tif (abs_ind == " + std::to_string(cur_idx) +
                ") return nndt_under(a" + std::to_string(cur_c) + ");\n";
    cur_idx++;
  }
  else // shape_type[0] == 'c' || shape_type[0] == 'l'
  {
    output << "\tif (abs_ind == " + std::to_string(cur_idx) + ") return a" +
                std::to_string(cur_c) + ";\n";
    cur_idx++;
    cur_c++;
  }

  for(size_t i = cur_idx; i < last_i; i++)
  {
    if(shape_type[i] == '*')
    {
      output << "\tif (abs_ind == " + std::to_string(cur_idx) +
                  ") return nndt_between(a" + std::to_string(cur_c - 1) + ",a" +
                  std::to_string(cur_c) + ");\n";
      cur_idx++;
    }
    else // shape_type[i] == 'c' || shape_type[i] == 'l'
    {
      output << "\tif (abs_ind == " + std::to_string(cur_idx) + ") return a" +
                  std::to_string(cur_c) + ";\n";
      cur_idx++;
      cur_c++;
    }
  }

  if(shape_type[last_i] == '*')
  {
    output << "\treturn nndt_above(a" + std::to_string(cur_c - 1) + ");\n";
  }
  else // shape_type[last_i] == 'c' || shape_type[last_i] == 'l'
  {
    output << "\tif (abs_ind == " + std::to_string(cur_idx) + ") return a" +
                std::to_string(cur_c) + ";\n";
  }
  output << "\tassert(0!=0);\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_prec(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  size_t num_concs = count_concs(shape_type);
  size_t shape_len = shape_type.length();

  output << "bool is_precise_" + std::to_string(spec_index) +
              "(size_t abs_ind,";

  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "size_t a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ") {\n";

  for(size_t i = 0; i < shape_len; i++)
  {
    if(shape_type[i] == 'c' || shape_type[i] == 'l')
    {
      output << "\tif(abs_ind == " + std::to_string(i) + ") return 1;\n";
    }
  }
  output << "\treturn 0;\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_add(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  size_t num_concs = count_concs(shape_type);

  output << "size_t add_" + std::to_string(spec_index) +
              "(size_t abs_ind, size_t num,";

  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "size_t a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ") {\n";
  output << "\tif (num == 0) return abs_ind;\n";
  output << "\tif (num == 1) {\n";

  output << "\t\tif (is_precise_" + std::to_string(spec_index) + "(abs_ind,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << "))\n";
  output << "\t\t\treturn abs_ind + 1;\n";
  size_t max = 2 * num_concs - 1;
  output << "\t\treturn (" + std::to_string(max) + " > ";
  output << "(a1 == 0)";
  for(size_t i = 1; i < num_concs; i++)
    output << "-(a" + std::to_string(i) + "+1==a" + std::to_string(i + 1) + ")";
  output << " || nndt_bool()) ? abs_ind : abs_ind + 1;\n";
  output << "\t}\n";
  output << "\tsize_t conc_idx = conc_" + std::to_string(spec_index) +
              "(abs_ind,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "\treturn abs_" + std::to_string(spec_index) + "(conc_idx + num,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_sub(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  size_t num_concs = count_concs(shape_type);

  output << "size_t sub_" + std::to_string(spec_index) +
              "(size_t abs_ind, size_t num,";

  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "size_t a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ") {\n";
  output << "\tif (num == 0) return abs_ind;\n";
  output << "\tif (num == 1) {\n";

  output << "\t\tif (is_precise_" + std::to_string(spec_index) + "(abs_ind,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ")) {\n";
  output << "\t\t\tif (abs_ind != 0)\n";
  output << "\t\t\t\treturn abs_ind - 1;\n";
  output << "\t\t\telse assert(0!=0);\n";
  output << "\t\t} else return (abs_ind == 0 || nndt_bool()) ? ";
  output << "abs_ind : abs_ind - 1;\n";
  output << "\t}\n";

  output << "\tsize_t conc_idx = conc_" + std::to_string(spec_index) +
              "(abs_ind,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "\tassert(conc_idx >= num);\n";
  output << "\treturn abs_" + std::to_string(spec_index) + "(conc_idx - num,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_mult(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  size_t num_concs = count_concs(shape_type);

  output << "size_t mult_" + std::to_string(spec_index) +
              "(size_t abs_ind, size_t num,";

  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "size_t a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ") {\n";
  output << "\tif (num == 0) return 0;\n";
  output << "\tif (num == 1) return abs_ind;\n";
  output << "\tsize_t conc_idx = conc_" + std::to_string(spec_index) +
              "(abs_ind,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "\treturn abs_" + std::to_string(spec_index) + "(conc_idx * num,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "}\n\n";
}
