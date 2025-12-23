#ifndef _WIN32
#  include <arpa/inet.h>
#endif

int main()
{
#ifndef _WIN32
  struct in_addr input;
  char *result = inet_ntoa(input);
  (void)*result;
#endif
  return 0;
}
