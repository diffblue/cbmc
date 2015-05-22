class A
{
}

class multinewarray
{
  public static void main(String[] args)
  {
    int x=10;
    int y=20;
    int[][] int_array = new int[x][y];
    
    for(int i=0; i<x; ++i)
      for(int j=0; j<x; ++j)
        int_array[i][j]=i+j;

    assert false;
    /*assert int_array[4][10] == 14;*/
    //A object_array[][] = new A[x][y];
  }
}

