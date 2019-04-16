public class C {

    public void test() {
        char[] c = Character.toChars(5);
        assert c.length == 1;
        assert c[0] == 5;

        char[] two_bytes = Character.toChars(0x10000);
        assert two_bytes.length == 2;
        assert two_bytes[0] == '\ud800';
        assert two_bytes[1] == '\udc00';
    }

    public void shouldFail() {
        char[] c = Character.toChars(20);
        assert c.length == 1;
        assert c[0] == 100;
    }

}
