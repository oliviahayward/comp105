;;;;;;;;;;;;;;;;;;; COMP 105 SCHEME II ASSIGNMENT ;;;;;;;;;;;;;;;
;; Olivia Hayward
;; COMP105
;; 3/2/2021

;;
;;  Problem 28
;;

;; Part B

(define greater (x y)
    (if (> x y)
        x
        y))

(define max* (xs)
    (foldr greater (car xs) xs))

    (check-expect (max* '(1 2 3 4)) 4)

;; Part E

(define sum (xs)
    (foldr + 0 xs))

(check-expect (sum '(1 2 3 4)) 10)
;; Part F

(define product (xs)
    (foldr * 1 xs))

(check-expect (product '(1 2 3 4)) 24)

;;
;;  Problem 29
;;

;; Part A

(define append (xs ys)
    (foldr cons ys xs))

(check-expect (append '(1 2 3) '(4 5 6)) '(1 2 3 4 5 6))

;; Part C

(define reverse (xs)
    (foldl cons '() xs))

(check-expect (reverse '(1 2 3)) '(3 2 1))

;;
;;  Problem 30
;;

(define map (f xs)
   (foldr (lambda (x xs) (cons (f x) xs)) '() xs))

    (check-expect (map (lambda (n) (* n n)) '(1 2 3 4)) '(1 4 9 16))
    (check-expect (map (lambda (n) (* n 2)) '(1 2 3 4)) '(2 4 6 8))

(define filter (p? xs)
    (foldr (lambda (x xs) (if (p? x) (cons x xs) xs)) '() xs))

    (check-expect (filter (lambda (n) (= (mod n 2) 0)) '(1 2 3 4)) '(2 4))

(define exists? (n xs)
    (foldr (lambda (x xs) (if (equal? n x) #t xs)) #f xs))

    (check-assert (exists? 3 '(1 2 3)))
    (check-assert (not (exists? 3 '(1 2 4))))

(define all? (p? xs)
    (foldr (lambda (x xs) (if (p? x) xs #f)) #t xs))

    (check-assert (all? number? '(1 2 3)))
    (check-assert (not (all? number? '(1 'Test 3))))


;;
;;  Problem 38
;;

;; Part A

(define member? (x s) (s x))
(val emptyset (lambda (x) #f))

;; laws
;; (evens x) == (= (mod x 2) 0)

(define evens (x) (= (mod x 2) 0))

;; Part B

;; laws
;; (two-digits (x) == ((x < 100) and (x > 9)))

(define two-digits (x) (and (< x 100) (> x 9)))

;; Part C

;; properties:
;; (member? x (add-element x s)) == #t
;; (member? x (add-element y s)) == #f, where (not (equal? y x))
;; (member? x (union s1 s2))     == #t, where x is in s1
;; (member? x (inter s1 s2))     == #f, where x is in s1 but not s2
;; (member? x (diff  s1 s2))     == #t, where x is in s1 but not s2

;; laws:
;; (define add-element x s) == (lambda (z) (|| (s z) (equal? x z))))
;; (define union s1 s2) == (lambda (z) (|| (s1 z) (s2 z))))
;; (define inter s1 s2) == (lambda (z) (&& (s1 z) (s2 z))))
;; (define diff s1 s2) == (lambda (z) (&& (s1 z) (not (s2 z)))))


(define add-element (x s) (lambda (z) (|| (s z) (equal? x z))))
(define union (s1 s2) (lambda (z) (|| (s1 z) (s2 z))))
(define inter (s1 s2) (lambda (z) (&& (s1 z) (s2 z))))
(define diff (s1 s2) (lambda (z) (&& (s1 z) (not (s2 z)))))

(check-assert (not (member? 1 evens)))
(check-assert (member? 2 evens))
(check-assert (member? 3 (add-element 3 evens)))
(check-assert (member? 33 (union evens two-digits)))

;; Part D

(record set-ops [emptyset member? add-element union inter diff])

(define set-ops-from (eq?)
   (let ([emptyset    (lambda (x) #f)]
         [member?     (lambda (x s) (s x))]
         [add-element (lambda (x s) (lambda (z) (|| (s z) (equal? x z))))]
         [union       (lambda (s1 s2) (lambda (z) (|| (s1 z) (s2 z))))]
         [inter       (lambda (s1 s2) (lambda (z) (&& (s1 z) (s2 z))))]
         [diff        (lambda (s1 s2) (lambda (z) (&& (s1 z) (not (s2 z)))))])
    (make-set-ops emptyset member? add-element union inter diff)))

(check-assert (function? set-ops-from))
(check-assert (set-ops? (set-ops-from =)))

(val atom-set-ops     (set-ops-from =))
(val atom-emptyset    (set-ops-emptyset    atom-set-ops))
(val atom-member?     (set-ops-member?     atom-set-ops))
(val atom-add-element (set-ops-add-element atom-set-ops)) 
(val atom-union       (set-ops-union       atom-set-ops))
(val atom-inter       (set-ops-inter       atom-set-ops))
(val atom-diff        (set-ops-diff        atom-set-ops))

(check-assert (atom-member? 3 (atom-add-element 3 two-digits)))
(check-assert (atom-member? 4 (atom-union evens two-digits)))
(check-assert (not (atom-member? 4 (atom-inter evens two-digits))))
(check-assert (atom-member? 24 (atom-inter evens two-digits)))
(check-assert (atom-member? 8 (atom-diff evens two-digits)))

;;
;;  Problem F
;;

;; laws:
;; ((flip f) x y) == (f y x)

(define flip (f)
    (lambda (n m) (f m n)))

(check-assert ((flip >) 3 4))
(check-expect ((flip append) '(1 2 3) '(4 5 6)) '(4 5 6 1 2 3))

;;
;;  Problem O
;;

;; (ordered-by? f) takes a function f and returns a function that checks whether
;;                 the list is ordered according to the comparison function
;;                 that was passed in

;; laws:
;; ((ordered-by? precedes?) '()) == #t
;; ((ordered-by? precedes?) '(x) == #t
;; ((ordered-by? precedes?) (cons x xs)) == (check (car xs) (cdr xs)), where xs
;;                                                  != null, if (f x (car xs))

(define ordered-by? (f)
    (letrec ([check (lambda (x xs) 
                        (if (null? xs)
                            #t
                            (if (f x (car xs))
                                (check (car xs) (cdr xs))
                                #f)))]
                [start   (lambda (xs)
                            (if (null? xs)
                                '()
                                (check (car xs) (cdr xs))))])
        start))

(check-assert (function? ordered-by?))
(check-assert (function? (ordered-by? >)))
(check-error (ordered-by? < '(1 2 3)))
(check-assert (not ((ordered-by? >) '(1 2 3))))
(check-assert ((ordered-by? <) '(1 2 3)))
(check-assert ((ordered-by? =) '(3 3 3)))
(check-assert (not ((ordered-by? =) '(3 3 32))))

;;
;;  Problem V
;;

(define bound-in? (key pairs)
  (if (null? pairs)
      #f
      (|| (= key (alist-first-key pairs))
          (bound-in? key (cdr pairs)))))

(val the-fault list1) ; build a singleton fault set
(val no-faults '())   ; an empty fault set

; ((faults/none) response) == no-faults

(define faults/none ()
    (lambda (x) (no-faults)))

; ((faults/always f) response) == (the-fault f)

(define faults/always (f)
    (lambda (x) (the-fault f)))


; ((faults/equal key value) response) == (the-fault key), where key = value in
;                                                            validator table t
; ((faults/equal key value) response) == (no faults), where key != value in
;                                                            validator table t

(define faults/equal (key value)
    (lambda (t) (if (equal? (find key t) value) (the-fault key) (no-faults))))


; (faults/both) == (union (validator1 x) (validator2 x))

(val faults/both
    (let* ([member?  (lambda (x s) (exists? ((curry =) x) s))]
           [add-elem (lambda (x s) (if (member? x s) s (cons x s)))]
           [union    (lambda (faults1 faults2)
                        (foldr add-elem faults2 faults1))])
        (lambda (v1 v2) (lambda (x) (union (v1 x) (v2 x))))))

; ((faults/switch key validators) response) == (find (find key t) validators)

(define faults/switch (key validators)
    (lambda (t) (find (find key t) validators)))

