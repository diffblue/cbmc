int main()
{
  1 << 1;                     // safe
  1 << -1;                    // unsafe, shift distance negative
  1 >> -1;                    // unsafe, shift distance negative
  1 << (sizeof(1) * 8);       // unsafe, shift distance too large
  1 << (sizeof(1) * 8 - 2);   // safe
  1u << (sizeof(1u) * 8 - 1); // safe
}
