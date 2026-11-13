int main()
{
  const char buf[4] = {};
  const char(&r)[4] = buf;
  // [expr.static.cast]/1: static_cast cannot cast away constness
  char *p = static_cast<char *>(r);
  return p != nullptr;
}
