
int main (void) {
  int x = 0;
  
  do{
    do{
      ++x;
    } while(0);

    if (x)
    {
      --x;
    }
  } while(0);

  return x;
}

