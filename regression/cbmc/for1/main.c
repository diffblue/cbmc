int main() {

  int i=0;
  
  for(;;)
  {
    i++;
    if(i==100) break;
  }
  
  assert(i==100);

  return 0;
}
