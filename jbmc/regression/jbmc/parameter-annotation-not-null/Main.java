import javax.validation.constraints.NotNull;

public class Main {
  public static Integer test1(boolean y, Object z, String[] s)
  {
    return foo(1, y, z, s);
  }
  public static Integer test2(Integer x, boolean y, Object z)
  {
    return new Main().bar(x, y, z, new String[0]);
  }
  public static Integer test3(boolean y)
  {
    return foo(new Integer(1), y, null, new String[0]);
  }
  public static Integer foo(@NotNull Integer x, @NotNull boolean y, Object z, @NotNull String[] s) {
    return x;
  }
  public Integer bar(@NotNull Integer x, @NotNull boolean y, Object z, @NotNull String[] s) {
    return x;
  }
}
