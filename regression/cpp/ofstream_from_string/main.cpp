// Compile-only guard for regression/cbmc-cpp/cpp11_ofstream_from_string:
// full verification currently times out in BMC (filebuf/locale state
// space), but the FRONT END must keep converting this cleanly (it was
// fixed 2026-07-22: destructor-chain thunk convention + locale/ios_base
// models).
#include <fstream>
#include <string>

int main()
{
  std::string name = "out.txt";
  auto out = std::ofstream{name};
  return 0;
}
