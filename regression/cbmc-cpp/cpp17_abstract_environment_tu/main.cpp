// Dog-food reproducer: CBMC's own
// src/analyses/variable-sensitivity/abstract_environment.cpp (named on
// the options line) fails to convert at its namespace-scope
//   static auto inverse_operations =
//     std::map<irep_idt, irep_idt>{{ID_equal, ID_notequal}, ...};
// with "initialisation of struct_tag requires initializer list, found
// symbol instead" and "cannot initialize type 'struct less' using
// value 'ID_equal'" -- a braced pair is routed to the map's COMPARATOR
// parameter instead of the initializer_list<value_type>.  A follow-up
// "symbol 'shared_ptr' does not uniquely resolve" appears downstream.
// The isolated shape (same declaration in a fresh TU with the same
// headers, /tmp probing and two cvise rounds) converts CLEAN -- the
// trigger needs this TU's earlier content, so this test names the real
// source file.
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  int reached = 1;
  __CPROVER_assert(reached == 1, "abstract_environment converts");
  return 0;
}
