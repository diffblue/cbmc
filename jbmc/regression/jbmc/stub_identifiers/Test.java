public class Test
{
  public static void f00(Opaque z)
  {
    try {
      Opaque x = new Opaque(Opaque.static_field);
      Opaque[] a = {Opaque.static_method(x.field), z};
      Opaque[] y = x.method(a);
      throw y[0];
    } catch(Opaque o) {
    }
  }
  public Opaque f01(Opaque z)
  {
    try {
      Opaque x = new Opaque(Opaque.static_field);
      Opaque[] a = {Opaque.static_method(x.field), z};
      Opaque[] y = x.method(a);
      throw y[0];
    } catch(Opaque o) {
      return o;
    }
  }
}
