#ifndef _WIN32
#include <arpa/inet.h>
#include <assert.h>

int main()
{
  uint32_t l;
  assert(l == ntohl(htonl(l)));

  uint16_t s;
  assert(s == ntohs(htons(s)));

  return 0;
}

#else

int main()
{
  return 0;
}

#endif
