(define-system Cnt 
    :input ((in (_ BitVec 8)))
    :output ((out (_ BitVec 8)))
    :init (= out #b00000001)
    :trans (= out' (bvadd out (bvsmod in #b00000011)))
)

;(define-system DoubleCnt 
;  :input ( (in Int) ) 
;  :output ( (out Int) )
;  :local ( (temp Int) )
;  :subsys  (C1 (Cnt in temp))
;  :subsys  (C2 (Cnt temp out))
;)

(check-system Cnt
    :input ((i (_ BitVec 8)))
    :output ((o (_ BitVec 8)))
    :assumption (a (= i #b00000010))
    :reachable (rch (= o #b00001010))
    :query (q (a rch))
)