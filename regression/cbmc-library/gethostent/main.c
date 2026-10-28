#include <assert.h>
#include <netdb.h>
#include <stddef.h>

int main(void)
{
  struct hostent *h = gethostent();
  // gethostent may return NULL (end of database or error).
  // On success, h_addr_list is a non-NULL, NULL-terminated array
  // with at least one entry.
  if(h != NULL && h->h_addr_list != NULL && h->h_addr_list[0] != NULL)
    assert(0); // reachable on any host with a /etc/hosts entry

  return 0;
}
