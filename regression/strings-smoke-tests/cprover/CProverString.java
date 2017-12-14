package org.cprover;

public final class CProverString {
    public static char charAt(String s, int i) {
        if (0 <= i && i < s.length())
            return s.charAt(i);
        else
            return '\u0000';
    }

    public static String substring(String s, int i) {
        if (i <= 0)
            return s;
        else if (i >= s.length())
            return "";
        else
            return s.substring(i);
    }

    public static String substring(String s, int i, int j) {
        if (i < 0)
            return substring(s, 0, j);
        if (j >= s.length())
            return substring(s, 0, s.length() - 1);
        if (i >= j)
            return "";
        return s.substring(i, j);
    }
}
