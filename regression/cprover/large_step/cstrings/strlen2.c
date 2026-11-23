__CPROVER_size_t strlen(const char *);

int main()
{
  strlen("foo"); // safe
  strlen(0);     // unsafe
}
