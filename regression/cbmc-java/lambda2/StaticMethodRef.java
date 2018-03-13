import java.util.function.Function;
import java.util.function.BiFunction;

public class StaticMethodRef{
 public Integer Smr(Integer ctr) {
  Function<Integer, Integer> func1 = Integer::valueOf;

    // Uses  Integer.valueOf(String)
  Function<String, Integer> func2 = Integer::valueOf;

  BiFunction<String, Integer, Integer> func3 = Integer::valueOf;

  if (ctr.equals(func1.apply(9)))
    return func1.apply(9);

  if (ctr.equals(func2.apply("8")))
    return func2.apply("8");

  if (ctr.equals(func3.apply("0111", 2)))
    return func3.apply("0111", 2);

  return ctr;
}
}
