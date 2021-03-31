;; SCHEME III ASSIGNMENT
;; Olivia Hayward
;; March 10, 2021

;;
;; Problem L
;;

;; (list-of? A? v) checks if the value provided is a list of which each element
;;                  satisfies A?

;; laws:
;; (list-of? A? '()) == #t 
;; (list-of? A? (cons x xs)) == (list-of? A? xs), where (list-of? A? x) = #t
;; (list-of? A? v) == (A? v)

(define list-of? (A? v)
    (if (null? v)
        #t
        (if (pair? v)
            (if (A? (car v))
                (list-of? A? (cdr v))
                #f)
            (A? v))))

    (check-assert (list-of? null? '()))
    (check-assert (not (list-of? null? #f)))
    (check-assert (list-of? number? '()))
    (check-assert (list-of? number? '(1 2 3)))
    (check-assert (not (list-of? number? '(hello 1))))
    (check-assert (not (list-of? number? '(2 hello 1))))
    (check-assert (list-of? function? (lambda (x) (* x x))))

;;
;; Problem F 
;;

;; (formula? v) checks whether the inputted value is a boolean formula

;; laws:
;; (formula? x) == #t, where x is a boolean value
;; (formula? (make-not f)) == (formula? (not-x v))
;; (formula? (make-or fs)) == (and (formula? (or-x v)) (formula? (or-y v)))
;; (formula? (make-and fs)) ==  (and (formula? (and-x v)) (formula? (and-y v)))
;; (formula? x) == #f, where x is not a symbol or boolean formula

(record not [x])
(record or [x y])
(record and [x y])

(define formula? (v)
    (if (boolean? v)
        #t
        (if (not? v)
            (formula? (not-x v))
            (if (or? v)
                (and (formula? (or-x v)) (formula? (or-y v)))
                (if (and? v)
                    (and (formula? (and-x v)) (formula? (and-y v)))
                    #f)))))

(check-assert (formula? #t))
(check-assert (not (formula? '(#f #t))))
(check-assert (formula? (make-not #f)))
(check-assert (formula? (make-or #t #f)))
(check-assert (not (formula? (make-or #t 8))))
(check-assert (formula? (make-and #t #f)))
(check-assert (not (formula? (make-not 85))))
(check-assert (not (formula? (lambda (x) (* x x)))))

;;
;; Problem E 
;;

;; (eval-formula f env) evaluates the formula and checks whether it is true
;;                      or false given the environment

;; laws:
;; (eval-formula x env) == x, where x is a symbol
;; (eval-formula (make-not f) env) == (if f #f #t)
;; (eval-formula (make-or f) env) == (or (find (or-x f) env)
;;                                                          (find (or-y f) env))
;; (eval-formula (make-and f) env) == (and (find (and-x f) env)
;;                                                         (find (and-y f) env))

(define eval-formula (f env)
    (if (boolean? f)
        f
        (if (not? f)
            (if f
                #f 
                #t)
            (if (or? f)
                (or (find (or-x f) env) (find (or-y f) env))
                (if (and? f)
                    (and (find (and-x f) env) (find (and-y f) env))
                    #f)))))


(check-assert (eval-formula (make-or 'x 'y) '((x #t) (y #f))))
(check-assert (not (eval-formula (make-and 'x 'y) '((x #t) (y #f)))))
(check-assert (not (eval-formula (make-not 'x) '((x #t) (y #f)))))
(check-assert (not (eval-formula 'x '((x #f)))))

;;
;; Problem S
;;

;; (find-formula-true-asst f fail succ) finds the assignments needed to make the
;;                          formula true

;; laws:
;; (find-formula-true-asst (f fail succ)) ==
;;                                        (find-formula-asst f #t '() fail succ)

;; (find-formula-asst x            bool cur fail succeed) == 
;;                  (find-formula-symbol x bool cur fail succeed),
;;                                                   where x is a symbol
;; (find-formula-asst (make-not f)  bool cur fail succeed) ==
;;      (find-formula-asst f (not bool) cur fail succeed)
                              
;; (find-formula-asst (make-or  fs) #t   cur fail succeed) == 
;;          (find-any-asst (fs) #t cur fail succeed)
;; (find-formula-asst (make-or  fs) #f   cur fail succeed) ==
;;          (find-all-asst (fs) #f cur fail succeed)
;; (find-formula-asst (make-and fs) #t   cur fail succeed) == 
;;          (find-all-asst (fs) #t cur fail succeed)
;; (find-formula-asst (make-and fs) #f   cur fail succeed) == 
;;          (find-any-asst (fs) #f cur fail succeed)

;; (find-all-asst '()         bool cur fail succeed) == (succeed cur fail)
;; (find-all-asst (cons f fs) bool cur fail succeed) == 
;;     (find-formula-asst fs bool cur fail (lambda (x y) (find-all-assist fs
;;                                                          bool x y succeed)))

;; (find-any-asst '()         bool cur fail succeed) == (fail)
;; (find-any-asst (cons f fs) bool cur fail succeed) ==
;;     (find-formula-asst fs bool cur (lambda () (find-any-assist fs bool
;;                                                  cur fail succeed)) succeed)

;; (find-formula-symbol x bool cur fail succeed) ==
;;                 (succeed (bind x bool cur) fail), where x is not bound in cur
;; (find-formula-symbol x bool cur fail succeed) == (succeed cur fail),
;;                                                        where x is bool in cur
;; (find-formula-symbol x bool cur fail succeed) == (fail),
;;                                                  where x is (not bool) in cur



(define find-formula-true-asst (f fail succ)
    (letrec ([find-formula-symbol (lambda (x bool cur fail succeed) (if (null?
                    (find x cur)) (succeed (bind x bool cur) fail)
                    (if (equal? (find x cur) bool) (succeed cur fail) (fail))))]
            [find-any-assist (lambda (f bool cur fail succeed) (if (null? f)
                (fail) (find-formula-asst (cdr f) bool cur (lambda ()
                    (find-any-assist (cdr f) bool cur fail succeed)) succeed)))]
            [find-all-assist (lambda (f bool cur fail succeed) (if (null? f)
                (succeed cur fail) (find-formula-asst (cdr f) bool cur fail
                   (lambda (x y) (find-all-assist (cdr f) bool x y succeed)))))]
            [find-formula-asst (lambda (f bool cur fail succeed) (if (symbol? f)
                (find-formula-symbol f bool cur fail succeed)
                (if (not? f) (find-formula-asst (not-x f) (not bool) cur fail
                    succeed)
                (if (or? f) (if (bool) (find-any-asst f #t cur fail succeed)
                    (find-all-asst f #f cur fail succeed))
                (if (and? f) (if (bool) (find-all-asst f #t cur fail succeed)
                             (find-any-asst f #f cur fail succeed)) (fail))))))]
    ) (find-formula-asst f #t '() fail succ)))
    
(check-assert (function? find-formula-true-asst))    ; correct name
(check-error (find-formula-true-asst))                ; not 0 arguments
(check-error (find-formula-true-asst 'x))             ; not 1 argument
(check-error (find-formula-true-asst 'x (lambda () 'fail)))   ; not 2 args
(check-error
   (find-formula-true-asst 'x (lambda () 'fail) (lambda (c r) 'succeed) 'z)) ; not 4 args
(check-error (find-formula-true-asst 'x (lambda () 'fail) (lambda () 'succeed)))
    ; success continuation expects 2 arguments, not 0
(check-error (find-formula-true-asst 'x (lambda () 'fail) (lambda (_) 'succeed)))
    ; success continuation expects 2 arguments, not 1
(check-error (find-formula-true-asst
                   (make-and (list2 'x (make-not 'x)))
                   (lambda (_) 'fail)
                   (lambda (_) 'succeed)))
    ; failure continuation expects 0 arguments, not 1

(check-expect   ; x can be solved
   (find-formula-true-asst 'x
                           (lambda () 'fail)
                           (lambda (cur resume) 'succeed))
   'succeed)

(check-expect   ; x is solved by '((x #t))
   (find-formula-true-asst 'x
                           (lambda () 'fail)
                           (lambda (cur resume) (find 'x cur)))
   #t)

(check-expect   ; (make-not 'x) can be solved
   (find-formula-true-asst (make-not 'x)
                           (lambda () 'fail)
                           (lambda (cur resume) 'succeed))
   'succeed)

(check-expect   ; (make-not 'x) is solved by '((x #f))
   (find-formula-true-asst (make-not 'x)
                           (lambda () 'fail)
                           (lambda (cur resume) (find 'x cur)))
   #f)