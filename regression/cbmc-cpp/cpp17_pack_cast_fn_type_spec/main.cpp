// The remaining layer of cpp17_function_handler_dispatch,
// header-free: in a partial specialization over a FUNCTION TYPE
// (W<R(Args...)>), a member whose parameter is the pack (Args...
// args) and whose body contains a pack-expanded functional cast
// `Args(args)...` fails conversion ("found no match for symbol
// 'Args'"), leaving the member bodyless.  The plain variadic class
// template form (W<Args...>) converts fine.  The shape of libstdc++
// std::function::operator()'s forwarding call.
// g++/clang++/valgrind run clean.

extern "C" void __CPROVER_assert(bool, const char *);
void sink(const int &, int &r) { r += 1; }
template <typename> struct W;
template <typename R, typename... Args> struct W<R(Args...)> {
  void run(Args... args) { sink(0, Args(args)...); }
};
int main() {
  int v = 41;
  W<void(int &)> w;
  w.run(v);
  __CPROVER_assert(v == 42, "pack cast dispatch");
  return 0;
}
