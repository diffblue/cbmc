void f(void * s1, void *s2)
{ 
  char *us1 = (char*) s1; 
  char *us2 = (char*) s2; 
  
  char us10=us1[0];
  char us20=us2[0];
  char us11=us1[1];
  char us21=us2[1];

  assert(us10=='a');  
  assert(us11=='b');  
  assert(us20=='g');
  assert(us21=='b');
} 

int main()
{ 
  char a[2][2]; 
  a[0][0] = 'a'; 
  a[0][1] = 'b'; 
  a[1][0] = 'g'; 
  a[1][1] = 'b'; 
  
  f(&a[0], &a[1]);
} 
