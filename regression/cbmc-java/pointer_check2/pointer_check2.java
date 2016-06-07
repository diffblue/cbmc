import java.util.*;

class pointer_check2
{
  public static void main(String[] args) 
  {
    String s = null;
    Random rand = new Random();
    int day = rand.nextInt(7); 

    if (day == 0)
    {
      s = "Monday";
    }
    else
    { 
      if (day == 1)
      {
        s = "Tuesday" ;
      }
    }
   System.out.println(s.length()); 
  }
}
