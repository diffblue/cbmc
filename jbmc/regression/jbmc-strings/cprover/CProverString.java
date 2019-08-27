package org.cprover;

public final class CProverString {
    public static char charAt(String s, int i) {
        if (0 <= i && i < s.length())
            return s.charAt(i);
        else
            return '\u0000';
    }

    public static int codePointAt(String s, int index) {
        return s.codePointAt(index);
    }

    public static int codePointBefore(String s, int index) {
        return s.codePointBefore(index);
    }

    public static int codePointCount(
            String s, int beginIndex, int endIndex) {
        return s.codePointCount(beginIndex, endIndex);
    }

    public static int offsetByCodePoints(
            String s, int index, int codePointOffset) {
        return s.offsetByCodePoints(index, codePointOffset);
    }

    public static CharSequence subSequence(
            String s, int beginIndex, int endIndex) {
        return s.subSequence(beginIndex, endIndex);
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

    public static StringBuilder append(
            StringBuilder sb, CharSequence cs, int i, int j) {
        return sb.append(cs, i, j);
    }

    public static StringBuilder delete(StringBuilder sb, int start, int end) {
        return sb.delete(start, end);
    }

    public static StringBuilder deleteCharAt(StringBuilder sb, int index) {
        return sb.deleteCharAt(index);
    }

    public static StringBuilder insert(
            StringBuilder sb, int offset, String str) {
        return sb.insert(offset, str);
    }

    public static StringBuilder insert(
            StringBuilder sb, int offset, boolean b) {
        return sb.insert(offset, b);
    }

    public static StringBuilder insert(
            StringBuilder sb, int offset, char c) {
        return sb.insert(offset, c);
    }

    public static StringBuilder insert(
            StringBuilder sb, int offset, int i) {
        return sb.insert(offset, i);
    }

    public static StringBuilder insert(
            StringBuilder sb, int offset, long l) {
        return sb.insert(offset, l);
    }

    public static StringBuilder insert(
            StringBuilder sb, int offset, float f) {
        return sb.insert(offset, f);
    }

    public static StringBuilder insert(
            StringBuilder sb, int offset, double d) {
        return sb.insert(offset, d);
    }

    public static void setLength(StringBuffer sb, int newLength) {
        sb.setLength(newLength);
    }

    public static char charAt(StringBuffer sb, int index) {
        return sb.charAt(index);
    }

    public static void setCharAt(StringBuffer sb, int index, char c) {
        sb.setCharAt(index, c);
    }

    public static StringBuffer delete(
            StringBuffer sb, int start, int end) {
        return sb.delete(start, end);
    }

    public static StringBuffer deleteCharAt(StringBuffer sb, int index) {
        return sb.deleteCharAt(index);
    }

    public static String substring(StringBuffer sb, int start, int end) {
        return sb.substring(start, end);
    }

    public static StringBuffer insert(
            StringBuffer sb, int offset, String str) {
        return sb.insert(offset, str);
    }

    public static StringBuffer insert(
            StringBuffer sb, int offset, boolean b) {
        return sb.insert(offset, b);
    }

    public static StringBuffer insert(
            StringBuffer sb, int offset, char c) {
        return sb.insert(offset, c);
    }

    public static StringBuffer insert(
            StringBuffer sb, int offset, int i) {
        return sb.insert(offset, i);
    }

    public static StringBuffer insert(
            StringBuffer sb, int offset, long l) {
        return sb.insert(offset, l);
    }

    public static String toString(int i) { return String.valueOf(i); }

    public static String toString(int i, int radix) {
      return Integer.toString(i, radix);
    }

    public static String toString(long l) { return String.valueOf(l); }

    public static String toString(long l, int radix) {
      return Long.toString(l, radix);
    }

    public static String toString(float f) { return String.valueOf(f); }

    public static String toString(double d) { return String.valueOf((float)d); }
}
