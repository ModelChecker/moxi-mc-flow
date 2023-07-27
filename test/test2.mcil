(define-system Delay 
    :input ((in (_ BitVec 1)))
    :output ((out (_ BitVec 1)))
    :trans (= out' in)
)

(check-system Delay
    :input ((i (_ BitVec 1)))
    :output ((o (_ BitVec 1)))
    :reachable (rch (= o #b0))
    :query (q (rch))
)

;(define-system DoubleCnt 
;  :input ( (in Int) ) 
;  :output ( (out Int) )
;  :local ( (temp Int) )
;  :subsys  (C1 (Cnt in temp))
;  :subsys  (C2 (Cnt temp out))
;)