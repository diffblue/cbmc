#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];

// character literals such as are of type int in C
STATIC_ASSERT(sizeof('a')==sizeof(int));

STATIC_ASSERT('\n' == 10);
STATIC_ASSERT('\0' == 0);
STATIC_ASSERT('\1' == 1);
STATIC_ASSERT('\144' == 100);
STATIC_ASSERT('\xff' == (char)0xff);

// wide ones
  
STATIC_ASSERT(L'\xff'==255);
STATIC_ASSERT(L'a'=='a');

#ifndef _WIN32
STATIC_ASSERT(L'\x12345678'==0x12345678L);
#endif

int main()
{
}
