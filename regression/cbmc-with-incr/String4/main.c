__CPROVER_size_t strlen(const char *s);

int main()
{
  assert(strlen("asdasd")==6);
  assert(strlen("")==0);
}
