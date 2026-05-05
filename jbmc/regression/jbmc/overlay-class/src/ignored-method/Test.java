import org.cprover.OverlayClassImplementation;
import org.cprover.IgnoredMethodImplementation;

@OverlayClassImplementation
public class Test
{
  @IgnoredMethodImplementation
  public static void main(String[] args)
  {
    assert(true);
  }
}
