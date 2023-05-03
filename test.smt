(define-system Cnt 
    :input ((in (_ BitVec 8)))
    :output ((out (_ BitVec 8)))
    :init (= out #b00000001)
    :trans (= out' (bvadd out (bvsmod in #b00000011)))
)

;(check-system Cnt
;    :input ((in0 (_ BitVec 8)))
;    :output ((out0 (_ BitVec 8)))
;    :reachable (rch (= out0 #b00001010))
;)