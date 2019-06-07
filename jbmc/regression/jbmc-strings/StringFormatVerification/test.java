import java.util.*;

public class test {

    public static void check_locale() {
        String s = String.format(Locale.ROOT, "foo %s", "bar");
        assert s.equals("foo bar");
    }

    public static void fail_locale() {
        String s = String.format(Locale.ROOT, "foo %s", "bar");
        assert !s.equals("foo bar");
    }

    public static void check_boolean() {
        String s = String.format("foo %b", true);
        assert s.equals("foo true");
    }

    public static void fail_boolean() {
        String s = String.format("foo %b", true);
        assert !s.equals("foo true");
    }

    public static void check_boolean_upper() {
        String s = String.format("foo %B", true);
        assert s.equals("foo TRUE");
    }

    public static void fail_boolean_upper() {
        String s = String.format("foo %B", true);
        assert !s.equals("foo TRUE");
    }

    public static void check_boolean_null() {
        Boolean bool = null;
        String s = String.format("foo %b", bool);
        assert s.equals("foo false");
    }

    public static void fail_boolean_null() {
        Boolean bool = null;
        String s = String.format("foo %b", bool);
        assert !s.equals("foo false");
    }

    public static void check_integer() {
        String s = String.format("foo %d", 13);
        assert s.equals("foo 13");
    }

    public static void fail_integer() {
        String s = String.format("foo %d", 13);
        assert !s.equals("foo 13");
    }

    public static void check_octal() {
        String s = String.format("foo %o", 13);
        assert s.equals("foo 15");
    }

    public static void fail_octal() {
        String s = String.format("foo %o", 13);
        assert !s.equals("foo 15");
    }

    public static void check_hex() {
        String s = String.format("foo %x", 13);
        assert s.equals("foo d");
    }

    public static void fail_hex() {
        String s = String.format("foo %x", 13);
        assert !s.equals("foo d");
    }

    public static void check_hex_upper() {
        String s = String.format("foo %X", 13);
        assert s.equals("foo D");
    }

    public static void fail_hex_upper() {
        String s = String.format("foo %X", 13);
        assert !s.equals("foo D");
    }

    public static void check_percent() {
        String s = String.format("foo %%");
        assert s.equals("foo %");
    }

    public static void fail_percent() {
        String s = String.format("foo %%");
        assert !s.equals("foo %");
    }

    public static void check_new_line() {
        String s = String.format("foo %n");
        assert s.equals("foo \n");
    }

    public static void fail_new_line() {
        String s = String.format("foo %n");
        assert !s.equals("foo \n");
    }

    public static void check_character() {
        String s = String.format("foo %c", 'c');
        assert s.equals("foo c");
    }

    public static void fail_character() {
        String s = String.format("foo %c", 'c');
        assert !s.equals("foo c");
    }

    public static void check_character_uppercase() {
        String s = String.format("foo %C", 'c');
        assert s.equals("foo C");
    }

    public static void fail_character_uppercase() {
        String s = String.format("foo %C", 'c');
        assert !s.equals("foo C");
    }

    public static void check_plus_sign() {
        String s = String.format("foo %+d", 13);
        assert s.equals("foo +13");
    }

    public static void fail_plus_sign() {
        String s = String.format("foo %+d", 13);
        assert !s.equals("foo +13");
    }

    public static void check_plus_sign_negative_value() {
        String s = String.format("foo %+d", -13);
        assert s.equals("foo -13");
    }

    public static void fail_plus_sign_negative_value() {
        String s = String.format("foo %+d", -13);
        assert !s.equals("foo -13");
    }

    public static void check_braces() {
        String s = String.format("foo %(d", -13);
        assert s.equals("foo (13)");
    }

    public static void fail_braces() {
        String s = String.format("foo %(d", -13);
        assert !s.equals("foo (13)");
    }

    public static void check_separators() {
        String s = String.format("foo %,d", 1000000);
        assert s.equals("foo 1,000,000");
    }

    public static void fail_separators() {
        String s = String.format("foo %,d", 1000000);
        assert !s.equals("foo 1,000,000");
    }

    public static void check_hash() {
        String s = String.format("foo %h", 13);
        assert s.equals("foo d");
    }

    public static void fail_hash() {
        String s = String.format("foo %h", 13);
        assert !s.equals("foo d");
    }

    public static void check_exponent() {
        String s = String.format("foo %e", 13.);
        assert s.equals("foo 1.300000e+01");
    }

    public static void fail_exponent() {
        String s = String.format("foo %e", 13.);
        assert !s.equals("foo 1.300000e+01");
    }

    public static void check_exponent_float_arg() {
        String s = String.format("foo %e", 13.0f);
        assert s.equals("foo 1.300000e+01");
    }

    public static void fail_exponent_float_arg() {
        String s = String.format("foo %e", 13.0f);
        assert !s.equals("foo 1.300000e+01");
    }

    public static void check_exponent_uppercase() {
        String s = String.format("foo %E", 13.);
        assert s.equals("foo 1.300000E+01");
    }

    public static void fail_exponent_uppercase() {
        String s = String.format("foo %E", 13.);
        assert !s.equals("foo 1.300000E+01");
    }

    public static void check_float() {
        String s = String.format("foo %f", 13.);
        assert s.equals("foo 13.000000");
    }

    public static void fail_float() {
        String s = String.format("foo %f", 13.);
        assert !s.equals("foo 13.000000");
    }

    public static void check_general_scientific() {
        String s = String.format("foo %g", 13.);
        assert s.equals("foo 13.0000");
    }

    public static void fail_general_scientific() {
        String s = String.format("foo %g", 13.);
        assert !s.equals("foo 13.0000");
    }

    public static void check_general_scientific_uppercase() {
        String s = String.format("foo %G", 13.);
        assert s.equals("foo 13.0000");
    }

    public static void fail_general_scientific_uppercase() {
        String s = String.format("foo %G", 13.);
        assert !s.equals("foo 13.0000");
    }

    public static void check_alternative() {
        String s = String.format("foo %a", 13.);
        assert s.equals("foo 0x1.ap3");
    }

    public static void fail_alternative() {
        String s = String.format("foo %a", 13.);
        assert !s.equals("foo 0x1.ap3");
    }

    public static void check_alternative_uppercase() {
        String s = String.format("foo %A", 13.);
        assert s.equals("foo 0X1.AP3");
    }

    public static void fail_alternative_uppercase() {
        String s = String.format("foo %A", 13.);
        assert !s.equals("foo 0X1.AP3");
    }

    public static void check_leading_spaces() {
        String s = String.format("foo % 5d", 13);
        assert s.equals("foo    13");
    }

    public static void fail_leading_spaces() {
        String s = String.format("foo % 5d", 13);
        assert !s.equals("foo    13");
    }

    public static void check_leading_zeros() {
        String s = String.format("foo %05d", 13);
        assert s.equals("foo 00013");
    }

    public static void fail_leading_zeros() {
        String s = String.format("foo %05d", 13);
        assert !s.equals("foo 00013");
    }
}
