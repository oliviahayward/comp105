; SAT Solver Test Cases 

(record not [arg])  
(record or  [args])
(record and [args])


; ¬x ∧ (x ∨ y)
(val f1 (make-and (make-not 'x) (make-or 'y 'x))
(val s1 '((x #f) (y #t)))

; ¬((x ∧ z) ∧ (x ∨ y))
(val f2 '(make-not (make-and (make-or 'x 'y) (make-and 'x 'z))) )
(val s2 '((x #f) (y #t) (z #f)) )

; ((x ∧ y) ∧ ((x ∨ z) ∧ (¬x)))
(val f3 '(make-and (make-and 'x 'y) (make-and (make-or 'x 'z) (make-not 'x))) )
(val s3 'no-solution )

