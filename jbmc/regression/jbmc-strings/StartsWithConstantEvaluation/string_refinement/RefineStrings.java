package string_refinement;

public class RefineStrings {
    public void constantComparison() {
        String helloWorld = "Hello world";
        assert helloWorld.equals(helloWorld());
        assert helloWorld.startsWith("Hello");
        assert helloWorld.startsWith("ello", 1);
        assert !helloWorld.startsWith("ello", -1);
    }

    public String helloWorld() {
        return "Hello world";
    }
}
