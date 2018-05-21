public class NullPointer2 {

  static Object my_field;

  public static void main(String[] args)
  {
    int z;
    
    z=my_field.hashCode(); // NULL pointer dereference 
  }

}
