public class Main {
    public void equals() {
        assert "abc".equalsIgnoreCase("ABC");
    }

    public void notEqual() {
        assert !"abce".equalsIgnoreCase("ABC");
    }

    public void noprop(String val) {
        assert val.equalsIgnoreCase("ABC");
    }

    public void longEquals() {
        assert !"abce".equalsIgnoreCase("qwertyuiops");
    }

    public void shortEquals() {
        assert !"abce".equalsIgnoreCase("BF");
    }

    public void nondetString(String str) {
        assert !str.equalsIgnoreCase("dave");
    }

    public void nondetArg(String str) {
        assert !"dave".equalsIgnoreCase(str);
    }

    public void pi() {
        assert !"π".equalsIgnoreCase("dave");
    }

    public void nonAlpha() {
        assert "^£&$1!".equalsIgnoreCase("^£&$1!");
    }

    public void empty() {
        assert "".equalsIgnoreCase("");
    }

    public void emptyThis() {
        assert !"".equalsIgnoreCase("dave");
    }

    public void emptyArg() {
        assert !"dave".equalsIgnoreCase("");
    }
}
