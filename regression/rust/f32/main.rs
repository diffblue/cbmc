fn main() {
  assert!(1.1 == 1.1 * 1.0);
  assert!(1.1 != 1.11 / 1.0);

  let a : f32;
  let b = a / 2.0;
  
  if a < 0.0 {
    assert!(a <= b);
  } else if a >= 0.0 {
    assert!(a >= b);
  }

  let c = b * 2.0;
  // general/infinity            Close but not exact                    NAN
  assert!(a == c || a - c < 0.00000001 || c - a < 0.00000001 || c * 0.0 != 0.0);

  let d : f32 = 0.0;
  assert!(d + 1.0 > 0.0);
  assert!(d - 1.0 < 0.0);
}
