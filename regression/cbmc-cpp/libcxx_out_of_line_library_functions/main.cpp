// libc++ declares these in its headers and defines them only in its compiled
// library: __shared_weak_count::__release_weak and lock (shared_ptr,
// weak_ptr), __next_prime (unordered containers), and the members of
// std::exception, std::bad_alloc and std::bad_array_new_length.  CBMC now
// supplies C++ models for them; calls had no body.
#include <memory>
#include <new>
#include <unordered_map>

extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::weak_ptr<int> w;
  {
    auto p = std::make_shared<int>(4);
    w = p;
    auto q = w.lock();
    __CPROVER_assert(q && *q == 4 && p.use_count() == 2, "lock while alive");
  }
  __CPROVER_assert(w.expired() && !w.lock(), "lock after expiry");

  std::unordered_map<int, int> m;
  m[1] = 2;
  __CPROVER_assert(m.at(1) == 2 && m.bucket_count() >= 1, "unordered_map");

  std::bad_array_new_length e;
  const std::exception &b = e;
  __CPROVER_assert(b.what() != nullptr, "what");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
