// Liveness canary for run_pass_by_value_check.sh.
//
// A single, self-contained F.16 pass-by-const-reference violation on a cheap
// type. The runner asserts that the freshly built checker reports exactly one
// finding here *before* scanning the tree, so that an outright tool failure
// (missing/broken LLVM, every TU failing to parse, ...) cannot masquerade as
// "no new pass-by-value violations" against the now-empty baseline.
//
// This file is intentionally not part of any build; it is fed to the checker
// directly with `-- -std=c++17`.

struct dstringt
{
  unsigned n;
};

typedef dstringt irep_idt;

// Exactly one violation: a cheap-to-copy type taken by const reference.
void canary(const irep_idt &);
