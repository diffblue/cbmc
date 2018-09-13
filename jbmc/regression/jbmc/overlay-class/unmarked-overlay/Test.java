import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

public class Test
{
  @OverlayMethodImplementation
  public static void main(String[] args)
  {
    assert(false);
  }
}
