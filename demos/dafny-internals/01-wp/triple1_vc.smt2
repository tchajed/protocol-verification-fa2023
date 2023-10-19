(declare-fun q () Int)

(assert
 (not
 ;; (q + q) + q = q * 3
  (= (+ (+ q q) q)
     (* q 3))
  ))
(check-sat)
