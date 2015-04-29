class what_not
{
};

class array1
{
  public static void main(String[] args)
  {
    int size=10;
    int int_array[]=new int[size];
    
    for(int i=0; i<size; i++)
      int_array[i]=i;

    what_not what_not_array[]=new what_not[size];
    
    //assert what_not_array.length == size;
    assert int_array[7] == 7;
  }
}

