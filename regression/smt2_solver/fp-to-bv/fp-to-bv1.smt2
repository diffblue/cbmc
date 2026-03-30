; Test fp.to_sbv and fp.to_ubv with various rounding modes.
; Previously crashed with non-RTZ rounding modes.

(set-logic QF_FP)

; fp.to_sbv RNE 41.5 == 42 (ties to even)
(assert (= ((_ fp.to_sbv 32) RNE
  (fp #b0 #b10000100 #b01001100000000000000000)) (_ bv42 32)))

; fp.to_ubv RTZ 3.125 == 3 (truncation)
(assert (= ((_ fp.to_ubv 32) RTZ
  (fp #b0 #b10000000 #b10010000000000000000000)) (_ bv3 32)))

(check-sat)
