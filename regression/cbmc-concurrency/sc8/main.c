int i, j;

int main()
{
  
  i++;
//  j++;
  
  __CPROVER_ASYNC_1: j++;
  
  assert(0);
  
  j++;
}
