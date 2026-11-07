// compressed_pair reference initialization fails for vector's
// internal allocator storage, preventing iterator_traits from
// being fully elaborated.
#include <vector>
int main()
{
  std::vector<int>::iterator it;
  (void)it;
}
