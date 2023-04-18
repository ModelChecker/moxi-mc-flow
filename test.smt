(define-system sys 
    :input ((in (_ BitVec 8)))
    :output ((out (_ BitVec 8)))
    :init (= out 0)
    :trans (= out' in)
)