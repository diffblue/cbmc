; fp.to_sbv with non-RTZ rounding mode
(set-logic QF_BVFP)
(assert (= ((_ fp.to_sbv 8) RTP ((_ to_fp 8 24) #x40200000)) #x03))
(check-sat)
