// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_to_string.h>

#include <solvers/smt2_incremental/smt_sorts.h>

#include <iostream>
#include <sstream>
#include <string>

class smt_sort_output_visitort : public smt_sort_const_downcast_visitort
{
protected:
  std::ostream &os;

public:
  explicit smt_sort_output_visitort(std::ostream &os) : os(os)
  {
  }

  void visit(const smt_bool_sortt &) override
  {
    os << "Bool";
  }

  void visit(const smt_bit_vector_sortt &bit_vec) override
  {
    os << "(_ BitVec " << bit_vec.bit_width() << ")";
  }
};

std::ostream &operator<<(std::ostream &os, const smt_sortt &sort)
{
  sort.accept(smt_sort_output_visitort{os});
  return os;
}

std::string smt_to_string(const smt_sortt &sort)
{
  std::stringstream ss;
  ss << sort;
  return ss.str();
}
