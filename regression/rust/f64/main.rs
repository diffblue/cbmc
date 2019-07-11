fn main() {
  let a : f64;
  let b = a / 2.0;
  
  if a < 0.0 {
    assert!(a <= b);
  } else if a >= 0.0 {
    assert!(a >= b);
  }

  let c = b * 2.0;
  // general/infinity            Close but not exact                    NAN
  assert!(a == c || a - c < 0.00000001 || c - a < 0.00000001 || c * 0.0 != 0.0);

  let d : f64 = 0.0;
  assert!(d + 1.0 > 0.0);
  assert!(d - 1.0 < 0.0);
}
