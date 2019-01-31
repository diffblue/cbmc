package string_refinement;

public class RefineStrings {
    public void constantComparison() {
        String helloWorld = "Hello world";
        assert helloWorld.equals(helloWorld());
    }

    public String helloWorld() {
        return "Hello world";
    }
}
