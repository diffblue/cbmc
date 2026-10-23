// Two instantiations of unordered_map::emplace for the SAME map type
// but with different argument value categories -- rvalues first
// (dstringt{}, unordered_set{}), then const lvalues obtained through a
// const_iterator -- make the second call fail with "found no match for
// symbol 'emplace'".  Each call converts fine in isolation; the value
// type must itself be an unordered container and the key must use a
// user hash specialization.  [over.match.funcs.general], [temp.deduct.call]:
// each call independently deduces its own _Args pack, so both
// specializations must resolve.  Distilled from
// goto-programs/restrict_function_pointers.cpp
// (merge_function_pointer_restrictions); blocks that dog-food TU.
#include <unordered_map>
#include <unordered_set>
extern "C" void __CPROVER_assert(bool, const char *);

class dstringt
{
public:
  dstringt() : no(0)
  {
  }
  bool operator==(const dstringt &o) const
  {
    return no == o.no;
  }
  unsigned no;
};

namespace std
{
template <>
struct hash<dstringt>
{
  size_t operator()(const dstringt &d) const
  {
    return d.no;
  }
};
} // namespace std

using restrictionst =
  std::unordered_map<dstringt, std::unordered_set<dstringt>>;

int main()
{
  restrictionst b;
  b.emplace(dstringt{}, std::unordered_set<dstringt>{});
  const restrictionst &cref = b;
  auto it = cref.begin();
  b.emplace(it->first, it->second);
  __CPROVER_assert(b.size() == 1, "emplace with mixed value categories");
  return 0;
}
