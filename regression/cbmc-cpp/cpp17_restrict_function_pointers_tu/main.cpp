// Dog-food reproducer: CBMC's own
// src/goto-programs/restrict_function_pointers.cpp (named on the
// options line) fails to convert at merge_function_pointer_
// restrictions' `result.emplace(restriction.first, restriction.second)`
// -- "found no match for symbol 'emplace'" instantiating
// unordered_map<irep_idt, unordered_set<irep_idt>>::emplace with
// <dstringt, unordered_set>.  The isolated shape (same typedef, same
// loop, fresh TU) converts CLEAN -- the trigger needs this TU's
// earlier content (json/options/goto_model headers), so this test
// names the real source file.  A second, independent error follows:
// std::ofstream{std::string} (see cpp11_ofstream_from_string).
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  int reached = 1;
  __CPROVER_assert(reached == 1, "restrict_function_pointers converts");
  return 0;
}
