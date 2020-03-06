/// \file
/// SMT-lib file interface, implemented using SMT-switch

#include <solvers/smt2/smt2_ifile.h>

smt2_ifilet::smt2_ifilet(
  std::ostream &_out)
  : out(_out)
  {}


void smt2_ifilet::set_logic(const std::string logic) const {
  out << "(set-logic " << logic << ")" << "\n";
}

void smt2_ifilet::set_opt(const std::string option, const std::string value) {
  out << "(set-option :" << option << " " << value << ")" << "\n";
}

smt::Result smt2_ifilet::check_sat() {
  out << "(check-sat)" << "\n";
  // This doesn't map very well to the abstraction, but we have to 
  // return something. TODO: Must be overwritten later. 
  return smt::ResultType::UNKNOWN;
}


void smt2_ifilet::write_comment(const std::string comment) {
  out << comment << "\n";
}

void smt2_ifilet::push(unsigned int num) {
  throw NotImplementedException("Incremental solving support has not been implemented yet.");
}

void smt2_ifilet::pop(unsigned int num) {
  throw NotImplementedException("Incremental solving support has not been implemented yet.");
}

smt::Sort smt2_ifilet::make_sort(const smt::SortKind sk) const {
  return smt::Sort{};
}

// TODO:
smt::Sort smt2_ifilet::make_sort(const smt::SortKind sk, uint64_t size) const {
  return smt::Sort{};
}

// TODO:
smt::Sort smt2_ifilet::make_sort(const std::string name,
                                 const unsigned int arity) const 
{
  return smt::Sort{};
}

void smt2_ifilet::assert_formula(const smt::Term &t) const
{
  // TODO
}

smt::Result smt2_ifilet::check_sat_assuming(const smt::TermVec &assumptions)
{
  return smt::ResultType::UNKNOWN; 
}

smt::Term smt2_ifilet::get_value(smt::Term &t) const
{
  return smt::Term{};
}

void smt2_ifilet::reset() {
  // TODO:
}

void smt2_ifilet::reset_assertions() {
  // TODO:
}

void smt2_ifilet::dump_smt2(FILE *file) const {
  // TODO:
}

smt::Term smt2_ifilet::substitute(const smt::Term term,
                         const smt::UnorderedTermMap &substitution_map)
{
  return smt::Term{};
}

smt::Term smt2_ifilet::lookup_symbol(const std::string name) const
{
  return smt::Term{};
}

bool smt2_ifilet::has_symbol(const std::string name) const
{
  return false; // TODO:
}

smt::Term smt2_ifilet::make_value(const smt::Term & val, const smt::Sort & sort) const
{
  return smt::Term{};
}

smt::Sort smt2_ifilet::make_sort(const smt::SortKind sk, const unsigned int size) const
{
  return smt::Sort{};
}

smt::Sort smt2_ifilet::make_sort(const smt::SortKind sk, const smt::Sort &sort1) const
{
  return smt::Sort{};
}

smt::Sort smt2_ifilet::make_sort(const smt::SortKind sk,
                        const smt::Sort &sort1,
                        const smt::Sort &sort2) const
{
  return smt::Sort{};
}

smt::Sort smt2_ifilet::make_sort(const smt::SortKind sk,
                        const smt::Sort &sort1,
                        const smt::Sort &sort2,
                        const smt::Sort &sort3) const
{
  return smt::Sort{};
}

smt::Sort smt2_ifilet::make_sort(const smt::SortKind sk, const smt::SortVec &sorts) const
{
  return smt::Sort{};
}

smt::Term smt2_ifilet::make_value(const std::string val,
                    const smt::Sort &sort,
                    unsigned int base) const
{
  return smt::Term{};
}

smt::Sort smt2_ifilet::make_sort(const smt::SortKind sk,
                        const std::vector<smt::Sort> &sorts,
                        const smt::Sort &sort) const
{
  return smt::Sort{};
}


smt::Term smt2_ifilet::make_value(const bool b) const
{
  return smt::Term{};
}

smt::Term smt2_ifilet::make_value(const unsigned int i, const smt::Sort & sort) const
{
  return smt::Term{};
}

smt::Term smt2_ifilet::make_term(const std::string name, const smt::Sort & sort)
{
  return smt::Term{};
}

smt::Term smt2_ifilet::make_term(const smt::Op op, const std::vector<smt::Term> & terms) const
{
  return smt::Term{};
}

smt::Term smt2_ifilet::make_term(const smt::Op op,
                        const smt::Term &t0,
                        const smt::Term &t1) const
{
  return smt::Term{};
}

smt::Term smt2_ifilet::make_term(const smt::Op op,
                        const smt::Term &t0,
                        const smt::Term &t1,
                        const smt::Term &t2) const
{
  return smt::Term{};
}

smt::Term smt2_ifilet::make_term(const smt::Op op, const smt::Term &t) const
{
  return smt::Term{};
}
