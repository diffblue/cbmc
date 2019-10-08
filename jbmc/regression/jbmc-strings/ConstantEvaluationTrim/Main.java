public class Main {
    public void trim() {
        String str = "   abc   ";
        str = str.trim();
        assert str.equals("abc");
    }

    public void noTrim() {
        String str = "   abc   ";
        str = str.trim();
        assert !str.equals(" abc ");
    }

    public void trimLeft() {
        String str = "   abc";
        str = str.trim();
        assert str.equals("abc");
    }

    public void trimRight() {
        String str = "abc   ";
        str = str.trim();
        assert str.equals("abc");
    }

    public void noprop(String str) {
        str = str.trim();
        assert str.equals("abc");
    }

    public void empty() {
        String str = "".trim();
        assert str.equals("");
    }

    public void tab() {
        String str = " ".trim();
        assert str.equals("");
    }

    public void linebreak() {
        String str = "\n".trim();
        assert str.equals("");
    }

    public void middleWhitespace() {
        String str = "  hello dave   ".trim();
        assert str.equals("hello dave");
    }
}
