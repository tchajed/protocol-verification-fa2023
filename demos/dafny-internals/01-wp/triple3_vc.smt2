(declare-fun q () Int)
(declare-fun i1 () Bool)
(declare-fun i2 () Bool)

(assert (not
         (let ((b1 (=>
                    (< q 5)
                    ; 12 = q * 3
                    (= 12 (* q 3))))
               (b2 (=>
                    (not (< q 5))
                    ;; q * 2 + q = q * 3
                    (= (+ (* q 2) q) (* q 3)))))
          ;; true is the new precondition (compared to triple2)
           (=> true (and (=> i1 b1) (=> i2 b2))))
         ))
(check-sat)
(get-model)
