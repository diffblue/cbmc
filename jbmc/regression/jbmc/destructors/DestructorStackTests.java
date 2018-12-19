import java.util.ArrayList;
import java.util.List;

public class DestructorStackTests {

    private class MinorClass {

    }

    public void mainTest(boolean unknown) {
        MinorClass minor1 = new MinorClass();
        if (unknown) {
            MinorClass minor2 = new MinorClass();
            try {
                MinorClass minor3 = new MinorClass();
            } catch (Exception ex) {
                MinorClass minor5 = new MinorClass();
                return;
            } finally {
                MinorClass minor4 = new MinorClass();
            }
        }

        List<String> strings = new ArrayList<>();
        strings.add("1");
        strings.add("2");
        strings.add("3");

        for (String val : strings) {
            if (val.equals("2"))
            {
                List<String> throwaway = new ArrayList<>();
                throwaway.add("34");
                break;
            }
            else if (val.equals("3"))
            {
                List<String> throwaway = new ArrayList<>();
                throwaway.add("23");
                continue;
            }
        }
    }
}
