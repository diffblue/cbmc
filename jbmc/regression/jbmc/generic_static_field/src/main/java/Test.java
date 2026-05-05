
public class Test<T> {

  public static Test<Integer> static_field;

  public static Test<Integer> test() {

    return static_field;

  }

}
