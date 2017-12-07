
int main()
{
  int i, j;

  if(i<=100 && j<i)
    assert(j<=100); 

  if(i<=100 && j<i)
    assert(j<101); 

  if(i<=100 && j<i)
    assert(j>100); // fails 

  if(i<=100 && j<i)
    assert(j<99); // fails 

  if(i<=100 && j<i)
    assert(j==100); // fails   
}
