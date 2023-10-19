(declare-fun q () Int)

(assert (not
         (let ((b1 (=>
                    (< q 5)
                    ; 12 = q * 3
                    (= 12 (* q 3))))
               (b2 (=>
                    (not (< q 5))
                    ;; q * 2 + q = q * 3
                    (= (+ (* q 2) q) (* q 3)))))
           (=> (< 3 q) (and b1 b2)))
         ))
(check-sat)
