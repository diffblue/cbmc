fn main() {
  let a : u32;
  assert!(            a / 2 <= a        );
  assert!(        a / 2 * 2 >= a / 2    );
  assert!(    a / 2 + 5 + 1 >  a / 2 + 5);
  assert!(a / 2 + 5 + 1 - 2 <  a / 2 + 5);
}
