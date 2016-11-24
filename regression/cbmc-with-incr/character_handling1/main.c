int isalnum(int c); 
int isalpha(int c); 
int isblank(int c); 
int iscntrl(int c); 
int isdigit(int c); 
int isgraph(int c); 
int islower(int c); 
int isprint(int c); 
int ispunct(int c); 
int isspace(int c); 
int isupper(int c); 
int isxdigit(int c); 
int tolower(int c); 
int toupper(int c);

int main()
{
  assert(isalnum('a'));
  assert(isalnum('1'));
  assert(isalnum('A'));
  assert(isalnum('G'));
  assert(!isalnum(' '));
  assert(!isalnum('.'));
  assert(!isalnum(0));
  
  assert(isalpha('a'));
  assert(!isalpha('1'));
  assert(isalpha('A'));
  assert(isalpha('G'));
  assert(!isalpha(' '));
  assert(!isalpha('.'));
  assert(!isalpha(0));
  
  assert(!isblank('a'));
  assert(!isblank('1'));
  assert(!isblank('A'));
  assert(!isblank('G'));
  assert(isblank(' '));
  assert(!isblank('.'));
  assert(!isblank(0));
  
  assert(!iscntrl('a'));
  assert(!iscntrl('1'));
  assert(!iscntrl('A'));
  assert(!iscntrl('G'));
  assert(!iscntrl(' '));
  assert(!iscntrl('.'));
  assert(iscntrl(0));
  
  assert(!isdigit('a'));
  assert(isdigit('1'));
  assert(!isdigit('A'));
  assert(!isdigit('G'));
  assert(!isdigit(' '));
  assert(!isdigit('.'));
  assert(!isdigit(0));
  
  assert(islower('a'));
  assert(!islower('1'));
  assert(!islower('A'));
  assert(!islower('G'));
  assert(!islower(' '));
  assert(!islower('.'));
  assert(!islower(0));
  
  assert(!isupper('a'));
  assert(!isupper('1'));
  assert(isupper('A'));
  assert(isupper('G'));
  assert(!isupper(' '));
  assert(!isupper('.'));
  assert(!isupper(0));
  
  assert(!isspace('a'));
  assert(!isspace('1'));
  assert(!isspace('A'));
  assert(!isspace('G'));
  assert(isspace(' '));
  assert(!isspace('.'));
  assert(!isspace(0));
  
  assert(tolower('a')=='a');
  assert(tolower('1')=='1');
  assert(tolower('A')=='a');
  assert(tolower('G')=='g');
  assert(tolower(' ')==' ');
  assert(tolower('.')=='.');
  assert(tolower(0)==0);
  
  assert(toupper('a')=='A');
  assert(toupper('1')=='1');
  assert(toupper('A')=='A');
  assert(toupper('G')=='G');
  assert(toupper(' ')==' ');
  assert(toupper('.')=='.');
  assert(toupper(0)==0);
  
}
