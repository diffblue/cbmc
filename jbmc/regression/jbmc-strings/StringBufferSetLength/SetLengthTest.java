public class SetLengthTest {

    public static void main(int unknown) {

        StringBuffer s = new StringBuffer("ABCD");
        // Avoid producing a huge string that consumes too much memory, or which
        // string refinement can't handle:
        if(unknown >= 100)
          return;

        try {
            s.setLength(unknown);
            assert s.length() == unknown;

            if(unknown > 4) {
                assert s.toString().startsWith("ABCD");
            }
            else if(unknown == 4) {
                assert s.toString().equals("ABCD");
            }
            else {
                assert "ABCD".startsWith(s.toString());
            }
        }
        catch (StringIndexOutOfBoundsException e) {
            assert unknown < 0;
        }
    }

}
