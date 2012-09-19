#include <wchar.h>
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
  
  // the following is a C11 UTF-8 string literal
  const char euro_sign[]=u8"\x20ac";
  assert((unsigned char)euro_sign[0]==0xe2);
  assert((unsigned char)euro_sign[1]==0x82);
  assert((unsigned char)euro_sign[2]==0xac);
  assert(euro_sign[3]==0);
  assert(sizeof(euro_sign)==4);

  // the following is C++ and C99  
  const wchar_t wide_amount[]=L"\u20AC123,00"; //€123,00
  assert(wide_amount[0]==0x20ac);
  assert(wide_amount[1]=='1');
  
  // C11 unicode string literals
  assert(sizeof(u8""[0])==sizeof(char));
  assert(sizeof(u""[0])==2);
  assert(sizeof(U""[0])==4);
}
