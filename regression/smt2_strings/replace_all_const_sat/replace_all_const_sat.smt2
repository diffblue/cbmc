(assert (= (str.replaceall "abcdefabcdef" "bc" "xy") "axydefaxydef"))
(check-sat)
