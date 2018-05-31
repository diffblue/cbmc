public class Opaque extends Exception
{
  public static Opaque static_field;
  public Opaque field;

  public Opaque(Opaque o) {
  }
  
  public static Opaque static_method(Opaque o) {
    return o;
  }

  public Opaque[] method(Opaque[] o) {
    return o;
  }
}
