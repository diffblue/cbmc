#include <sstream>
#include <vector>

#include <namespace.h>
#include <smt.h>

// TODO: Document the calls

class smt2_ifilet : public smt::AbsSmtSolver {
  private:
    std::ostream &out;
  
  public:
    smt2_ifilet(std::ostream &_out);

    void set_opt(const std::string option, const std::string value);

    void set_logic(const std::string logic) const;

    void assert_formula(const smt::Term &t) const;

    void write_comment(const std::string comment);

    smt::Result check_sat();

    smt::Result check_sat_assuming(const smt::TermVec &assumptions);

    void push(unsigned int num = 1) override;

    void pop(unsigned int num = 1) override;

    smt::Term get_value(smt::Term &t) const;

    // SMT Sorts constructors
    smt::Sort make_sort(const smt::SortKind sk) const;

    smt::Sort make_sort(const smt::SortKind sk, uint64_t size) const;

    smt::Sort make_sort(const smt::SortKind sk, const unsigned int size) const;

    smt::Sort make_sort(const std::string name,
                         const unsigned int arity) const;

    smt::Sort make_sort(const smt::SortKind sk, const smt::Sort &sort1) const;

    smt::Sort make_sort(const smt::SortKind sk,
                        const smt::Sort &sort1,
                        const smt::Sort &sort2) const;

    smt::Sort make_sort(const smt::SortKind sk,
                        const smt::Sort &sort1,
                        const smt::Sort &sort2,
                        const smt::Sort &sort3) const;

    smt::Sort make_sort(const smt::SortKind sk, const smt::SortVec &sorts) const;

    // SMT Term constructors
    smt::Term make_term(bool b) const;

    smt::Term make_term(int64_t i, const smt::Sort &sort) const;

    smt::Term make_symbol(const std::string name, const smt::Sort &sort);

    smt::Term make_term(const smt::Op op, const smt::Term &t) const;

    smt::Term make_term(const smt::Op op,
                        const smt::Term &t0,
                        const smt::Term &t1) const;
    
    smt::Term make_term(const smt::Op op,
                        const smt::Term &t0,
                        const smt::Term &t1,
                        const smt::Term &t2) const;

    smt::Term make_value(const bool b) const;

    smt::Term make_value(const unsigned int i, const smt::Sort & sort) const;

    smt::Term make_value(const std::string val,
                    const smt::Sort &sort,
                    unsigned int base = 10) const;
    
    smt::Term make_value(const smt::Term & val, const smt::Sort & sort) const;

    // smt::Term make_term(const smt::Op op, const smt::TermVec & terms) const;

    smt::Sort make_sort(const smt::SortKind sk,
                        const std::vector<smt::Sort> &sorts,
                        const smt::Sort &sort) const;

    smt::Term make_term(const std::string name, const smt::Sort & sort);

    smt::Term make_term(const smt::Op op, const std::vector<smt::Term> & terms) const;

    smt::Term lookup_symbol(const std::string name) const;

    bool has_symbol(const std::string name) const;

    void reset();

    void reset_assertions();

    smt::Term substitute(const smt::Term term,
                         const smt::UnorderedTermMap &substitution_map);

    void dump_smt2(FILE *file) const;

    bool get_interpolant(const smt::Term &A,
                         const smt::Term &B,
                               smt::Term &out_I) const
    {
      throw NotImplementedException("Interpolants are not supported by this solver.");
    }
};
