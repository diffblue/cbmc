extern "C" void __CPROVER_assert(bool, const char *);

#include <cstddef>

// a flexible array member (C11 6.7.2.1/18; a GNU extension in C++, used by
// glibc's struct cmsghdr) contributes no size
struct header
{
  unsigned long len;
  int level;
  unsigned char data[];
};

// the shape of glibc's __cmsg_nxthdr
static header *next(header *h, unsigned char *end)
{
  unsigned char *n =
    reinterpret_cast<unsigned char *>(h) + sizeof(header) +
    ((h->len + sizeof(unsigned long) - 1) & ~(sizeof(unsigned long) - 1));
  if(n + sizeof(header) > end)
    return 0;
  return reinterpret_cast<header *>(n);
}

int main()
{
  __CPROVER_assert(
    sizeof(header) == 2 * sizeof(unsigned long) &&
      offsetof(header, data) == sizeof(unsigned long) + sizeof(int),
    "sizeof");

  alignas(header) unsigned char buffer[3 * sizeof(header)];
  header *h = reinterpret_cast<header *>(buffer);
  h->len = 3;
  h->data[2] = 7;
  __CPROVER_assert(buffer[offsetof(header, data) + 2] == 7, "element");
  __CPROVER_assert(
    next(h, buffer + sizeof(buffer)) ==
      reinterpret_cast<header *>(buffer + sizeof(header) + 8),
    "next header");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
