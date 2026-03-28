/// \file
/// Soundness argument for may-alias concurrent pointer dereferences
///
/// Background: Alglave/Kroening/Tautschnig, "Partial Orders for Efficient
/// Bounded Model Checking of Concurrent Software", CAV 2013.
///
/// == Problem ==
///
/// When a shared pointer `ptr` is dereferenced in a concurrent program,
/// the value set may not accurately reflect all possible targets because
/// other threads may have modified `ptr`. The standard approach of
/// consulting the value set and creating a conditional expression
/// (ptr == &o1 ? o1 : ptr == &o2 ? o2 : ...) is unsound because the
/// value set is computed per-thread and doesn't account for inter-thread
/// writes to `ptr`.
///
/// == Solution: May-Alias Objects ==
///
/// Instead of consulting the value set, we create a fresh symbol
/// `concurrency::may_alias$N` of the pointed-to type. This symbol
/// represents "whatever ptr points to" and participates in the
/// partial-order constraints as follows.
///
/// == Formal Argument ==
///
/// Let `m` be the may-alias read event for `*ptr`, and let `ptr_read`
/// be the L2-renamed SSA symbol for the read of `ptr` at the dereference
/// point. The value of `ptr_read` is determined by the read-from relation
/// for `ptr` (i.e., which write to `ptr` this read sees).
///
/// For each concrete address `a` with representative object `obj_a`:
///
/// 1. ALIAS CONDITION: alias(m, a) ≡ pointer_object(ptr_read) = pointer_object(&obj_a)
///    This is true iff `ptr` points to `obj_a` in the current execution.
///
/// 2. READ-FROM (rf-val, rf-some):
///    For each write `w` to address `a`:
///      s_{w,m} ⇒ alias(m, a) ∧ val(w) = val(m)
///    The rf-some constraint is:
///      alias(m, a) ⇒ ∨_w s_{w,m}
///    This says: IF ptr points to obj_a, THEN m must read from some write
///    to obj_a. If ptr does NOT point to obj_a, the constraint is vacuous.
///
///    CORRECTNESS: In any valid execution where ptr points to obj_a,
///    the may-alias read sees the value of obj_a as determined by the
///    write serialisation. If ptr doesn't point to obj_a, the may-alias
///    read is unconstrained w.r.t. obj_a (correct, since it reads from
///    a different address).
///
/// 3. WRITE SERIALISATION (ws-ext):
///    For may-alias writes w_m to address a:
///      alias(w_m, a) ∧ alias(w', a) ∧ s ⇒ before(w_m, w')
///      alias(w_m, a) ∧ alias(w', a) ∧ ¬s ⇒ before(w', w_m)
///    The alias conditions ensure that write serialisation only applies
///    when the may-alias write actually targets address a.
///
/// 4. FROM-READ (fr):
///    For may-alias read m at address a:
///      alias(m, a) ∧ s_{w',m} ∧ before(w', w) ⇒ before(m, w)
///    The alias condition ensures from-read only applies when the
///    may-alias read actually targets address a.
///
/// 5. INIT WRITES:
///    May-alias addresses do NOT get init writes. Their initial value
///    is determined by the aliasing: if ptr points to obj_a, the
///    may-alias read sees obj_a's value (including its init write).
///
/// == Soundness Theorem (sketch) ==
///
/// Claim: For any satisfying assignment V of (ssa ∧ pord), there exists
/// a valid execution of the original program (without may-alias objects)
/// that produces the same observable behaviour.
///
/// Proof sketch:
/// - V determines a value for ptr_read (via rf for ptr).
/// - This value equals &obj_a for some concrete object obj_a.
/// - The alias condition alias(m, a) is true, and alias(m, b) is false
///   for all b ≠ a.
/// - The rf-some constraint forces m to read from some write to obj_a.
/// - The rf-val constraint forces val(m) = val(w) for the selected write.
/// - Therefore val(m) equals the value of obj_a as seen through the
///   memory model — exactly what *ptr would read in the original program.
/// - The ws and fr constraints for m at address a are equivalent to the
///   constraints that would exist for a direct read of obj_a.
/// - The ws and fr constraints for m at other addresses b are vacuous
///   (guarded by false alias conditions).
/// - Therefore the partial order constraints for m are equivalent to
///   those for a direct read of obj_a, and the execution is valid.
///
/// Claim: For any valid execution of the original program, there exists
/// a satisfying assignment of (ssa ∧ pord).
///
/// Proof sketch:
/// - In the execution, *ptr reads from some concrete object obj_a.
/// - Set ptr_read = &obj_a (via the rf for ptr).
/// - Set val(m) = val(obj_a) as determined by the execution's rf.
/// - The alias condition alias(m, a) is true.
/// - The rf-some, rf-val, ws, and fr constraints for m at address a
///   are satisfied by the same clock assignment as for a direct read
///   of obj_a in the original execution.
/// - The constraints for m at other addresses are vacuously satisfied.
/// - Therefore (ssa ∧ pord) is satisfiable.
///
/// == Limitations ==
///
/// 1. SHARED POINTER ONLY: The may-alias mechanism only triggers when
///    the pointer expression directly contains a shared (global or dirty)
///    symbol. A local pointer assigned from a shared source uses the
///    standard value-set dereference, which may be unsound.
///    Example: `int *local = shared_ptr; *local` uses value-set.
///    Fix: Track "tainted" pointers — any local assigned from a shared
///    expression inherits the shared property. Alternatively, treat all
///    pointer dereferences as potentially shared in multi-threaded mode
///    (conservative but simple; increases formula size).
///
/// 2. POINTER-OBJECT GRANULARITY: The alias condition uses
///    pointer_object equality, which checks object identity but not
///    offset within the object. This is the correct granularity for
///    the may-alias mechanism: the may-alias object represents the
///    entire pointed-to object, and offsets are handled by the
///    byte_extract/byte_update operations in the SSA equation.
///    Field sensitivity means struct members and array elements get
///    separate addresses in the memory model, so this is precise
///    for the common case. The only imprecision is for byte-level
///    pointer arithmetic within a single field, which is rare in
///    concurrent code.
///
/// 3. TYPE COMPATIBILITY: May-alias events are only distributed to
///    addresses with exactly matching types. This prevents crashes
///    from type-mismatched value equality constraints in the memory
///    model. Relaxing to same-size types requires adding typecasts
///    to the rf-val constraints (s_{w,r} ⇒ val(w) = val(r)), which
///    is a deeper change to the memory model. In practice, concurrent
///    code almost always uses consistent types for shared data, so
///    this limitation rarely causes missed bugs.
