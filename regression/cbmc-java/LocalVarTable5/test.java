

public class test
{
  public static void main(int unknown)
  {
    int i;
    int j;
    if(unknown==1)
    {
      // Check that anonymous locals
      // get assigned scopes:
      i = 0;
      i++;
    }
    else if(unknown==2)
    {
      j = 0;
      j++;
    }
    else
    {
      // Check that temporaries (here
      // a new_tmp variable) are treated
      // likewise
      test t = new test();
    }
  }
}
