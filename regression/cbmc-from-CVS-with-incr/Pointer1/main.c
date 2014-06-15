int main()
 {
  int a, b, c, *p; 
 
  if(c) p=&a; else p=&b;
  
  *p=3;
  
  assert(b==3 || a==3);
 }
