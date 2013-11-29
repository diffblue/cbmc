int main() {
  int i;
  
  for(i=0; i<10; i++) {
    const int a=i;
  }
  
  int array[10];
  for(i=0; i<10; i++)
  {
    const int a;
    array[i]=a;
  }
   
  // these should all be allowed to be different
  assert(array[0]==array[1]);
}
