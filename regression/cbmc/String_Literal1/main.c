#include <assert.h>

int main()
{
  assert(""[0]==0);
  assert("\033\\"[0]==27);
  assert("\033\\"[1]=='\\');
  assert("\xcZ\\"[0]==12);
  assert("\xcZ\\"[1]=='Z');
  assert("\""[0]=='"');
  assert("\%"[0]=='%');
  assert("\n"[0]==10);
  
  // wide strings
  assert(L"abc"[0]=='a');
  assert(L"abc"[1]=='b');
  assert(L"abc"[3]==0);
  assert(L"\x1234"[0]==0x1234);
}
