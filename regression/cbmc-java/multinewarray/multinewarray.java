class A
{
}

class multinewarray
{
  public static void main(String[] args)
  {
    int[][][] some_a = new int[4][3][2];

    assert some_a.length==4;
    assert some_a[0].length==3;
    assert some_a[0][0].length==2;
  
    int x=10;
    int y=20;
    int[][] int_array = new int[x][y];
    
    for(int i=0; i<x; ++i)
      for(int j=0; j<x; ++j)
        int_array[i][j]=i+j;

    //assert false;
    /*assert int_array[4][10] == 14;*/
    //A object_array[][] = new A[x][y];
  }
}

