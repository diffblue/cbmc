public class StringUtil {
  public static String getLastToken(
      String toSplit, char delimiter, int limit) {
    if(toSplit == null) {
      return null;
    }
    int numberOfTokens = 0;
    int tokenStart = 0;
    int tokenEnd = toSplit.indexOf(delimiter, tokenStart);
    while (tokenEnd != -1 && numberOfTokens < limit - 1) {
      ++numberOfTokens;
      tokenStart = tokenEnd + 1;
      tokenEnd = toSplit.indexOf(delimiter, tokenStart);
    }
    ++numberOfTokens;
    String lastToken = toSplit.substring(tokenStart, toSplit.length());
    assert(lastToken.indexOf(delimiter) < 0 || numberOfTokens == limit);
    return lastToken;
  }
}
