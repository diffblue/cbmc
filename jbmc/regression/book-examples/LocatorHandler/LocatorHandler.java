public class LocatorHandler {
  public enum LocatorType {XPATH, ID; }
  public static Locator autoLocator(String locator, LocatorType type) {
    switch (type) {
    case XPATH:
      if (locator.startsWith("xpath=")) {
        assert(false);
        locator = locator.substring(locator.indexOf("=") + 1);
      }
      return new XPathLocator(locator);
    case ID:
      if (locator.startsWith("id=")) {
        assert(false);
        locator = locator.substring(locator.indexOf("=") + 1);
      }
      return new IdLocator(locator);
    }
    return null;
  }
}
