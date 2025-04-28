// Using a forward declaration rather than including netdb.h to make sure we do
// not have the compiled body of functions from header files available right
// away.
struct hostent;
struct hostent *gethostbyname(const char *name);

int main()
{
  (void)gethostbyname("x");
}
