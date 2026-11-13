// N5008 [debugging.utility]: libstdc++ 16 declares these in <debugging> and
// defines them in libstdc++exp.  Whether a debugger is present is not known
// (/4), breakpoint() returns (/1, implementation-defined), and
// breakpoint_if_debugging() is `if(is_debugger_present()) breakpoint();' (/2).
extern "C" void __CPROVER_assert(bool, const char *);
namespace std
{
bool is_debugger_present() noexcept;
void breakpoint() noexcept;
void breakpoint_if_debugging() noexcept;
} // namespace std
int main()
{
  int present = 0, absent = 0;
  for(int i = 0; i < 2; ++i)
  {
    if(std::is_debugger_present())
      ++present;
    else
      ++absent;
  }
  std::breakpoint();
  std::breakpoint_if_debugging();
  __CPROVER_assert(present + absent == 2, "both return");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
