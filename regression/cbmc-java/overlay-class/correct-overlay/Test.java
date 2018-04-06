import com.diffblue.OverlayClassImplementation;
import com.diffblue.OverlayMethodImplementation;

@OverlayClassImplementation
public class Test
{
  public int x;

  @OverlayMethodImplementation
  public static void main(String[] args)
  {
    assert(true);
  }
}
