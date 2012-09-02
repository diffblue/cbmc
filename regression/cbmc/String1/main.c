#include <assert.h>

char s[]="abc\001";

char *p="abc";

int input;

int main()
{
  assert(s[1]=='b');
  assert(s[4]==0);
  
  // write to s
  s[0]='x';
  
  assert(p[2]=='c');
  
  p=s;

  // write to p
  p[1]='y';
  
  assert(s[1]=='y'); 

  {
    const char local_string[]="asd123";

    assert(local_string[0]=='a');
    assert(sizeof(local_string)==7);
    assert(local_string[6]==0);
  }

  // wide strings
  #ifdef _WIN32
  // Visual Studio has a built-in wchar_t
  typedef wchar_t wide_char_type;
  #else
  typedef __typeof__(L'X') wide_char_type;
  #endif
  
  unsigned width=sizeof(wide_char_type);

  #ifdef _WIN32  
  assert(width==2);
  #else
  assert(width==4);
  #endif
  
  assert(sizeof(L"12" "34")==5*width);
  assert(sizeof("12" L"34")==5*width);

  wide_char_type wide[]=L"1234\x0fff";
  assert(sizeof(wide)==6*width);
  assert(wide[4]==0x0fff);
}
