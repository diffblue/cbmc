void *malloc(__CPROVER_size_t);

int main(int argc, char** argv)
{
  char* c=(char*)malloc(10);
  char* d=c;
  for(char i=0; i<10; i++, d++);
  __CPROVER_assert((__CPROVER_size_t)d == (__CPROVER_size_t)c + 10, "");
}
