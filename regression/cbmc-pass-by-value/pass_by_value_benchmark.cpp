// Microbenchmark: passing irep_idt by value vs. by const reference.
//
// Motivation
// ----------
// irep_idt is a dstringt, i.e. a single 4-byte unsigned table index. The F.16
// cleanup (passing it by value rather than by const reference) raised the
// question of whether by-value is actually faster. This benchmark answers
// that at the calling-convention level.
//
// How it works
// ------------
// Two functions do identical work (`return a == b;`) but differ only in how
// they take their irep_idt arguments: by value vs. by `const irep_idt &`.
// Both are marked __attribute__((noinline)) so the compiler is forced to
// honour the calling convention rather than inlining the difference away
// (by-value passes the 4-byte index in a register; by-const-reference passes
// a pointer that the callee must dereference). We then call each ~3e8 times
// over an array of real irep_idts and time the two loops with a steady clock.
// The accumulator and a volatile sink keep the calls from being optimised out.
//
// Build & run
// -----------
//   g++ -O2 -std=c++17 -Isrc \
//     regression/cbmc-pass-by-value/pass_by_value_benchmark.cpp \
//     -Wl,--start-group build/lib/libutil.a build/lib/libbig-int.a \
//     -Wl,--end-group -o /tmp/pass_by_value_benchmark
//   /tmp/pass_by_value_benchmark
// (any directory with a built libutil.a / libbig-int.a works).
//
// Result (5 runs, ubuntu-24.04, g++ -O2; very stable)
// ---------------------------------------------------
//   calls each: ~3.0e8
//   by-value: ~443 ms
//   by-ref:   ~443 ms     (difference < 0.3 %, within run-to-run noise)
//
// Conclusion: at the calling-convention level the change is
// performance-neutral -- the by-reference indirection is a single extra load
// that is lost in loop/call overhead, and in any real caller it is dwarfed by
// what the callee does (e.g. a symbol_table lookup). This PR is therefore
// motivated by correctness (it exposed and fixed a latent dangling-reference
// bug) and C++ Core Guidelines F.16 alignment, not by a measurable speed-up.

#include <util/irep.h>

#include <chrono>
#include <cstdio>
#include <string>
#include <vector>

static volatile unsigned long sink = 0;

// noinline so the by-value vs by-const-reference calling convention is
// actually exercised (otherwise the compiler inlines both identically).
__attribute__((noinline)) static bool by_value(irep_idt a, irep_idt b)
{
  return a == b;
}

__attribute__((noinline)) static bool
by_ref(const irep_idt &a, const irep_idt &b)
{
  return a == b;
}

int main()
{
  std::vector<irep_idt> ids;
  for(int i = 0; i < 1000; i++)
    ids.push_back(irep_idt("id_" + std::to_string(i % 500)));
  const std::size_t N = ids.size();
  const long iters = 300000;

  unsigned long acc = 0;

  auto t0 = std::chrono::steady_clock::now();
  for(long it = 0; it < iters; it++)
    for(std::size_t i = 0; i + 1 < N; i++)
      acc += by_value(ids[i], ids[i + 1]);
  auto t1 = std::chrono::steady_clock::now();

  for(long it = 0; it < iters; it++)
    for(std::size_t i = 0; i + 1 < N; i++)
      acc += by_ref(ids[i], ids[i + 1]);
  auto t2 = std::chrono::steady_clock::now();

  sink = acc;

  const double by_value_ms =
    std::chrono::duration<double, std::milli>(t1 - t0).count();
  const double by_ref_ms =
    std::chrono::duration<double, std::milli>(t2 - t1).count();
  std::printf(
    "calls each: %ld\nby-value: %8.1f ms\nby-ref:   %8.1f ms\nacc=%lu\n",
    iters * (long)(N - 1),
    by_value_ms,
    by_ref_ms,
    acc);
  return 0;
}
