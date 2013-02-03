int main()
{
  #ifdef _MSC_VER

  // Visual Studio won't even parse the stuff below

  #else

  // the following is ok in C99 and upwards
  
  for(unsigned i=0; i<10; i++);  
  for(char i=0; i<10; i++);
  
  #endif
}
