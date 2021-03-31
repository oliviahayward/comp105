;;;;;;;;;;;;;;;;;;; COMP 105 SCHEME ASSIGNMENT ;;;;;;;;;;;;;;;
;; Olivia Hayward
;; COMP105
;; 2/23/2021
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise 1

;; (check-next xs ys) checks if car xs equals car ys. If so, it checks the next
;; pair until either the sublist is empty or it finds a discrepency.

;; laws:
;;   (check-next xs ys) == #t, where xs is null
;;   (check-next xs ys) == #f, where ys is null
;;   (check-next xs ys) == (check-next (cdr xs) (cdr ys)),
;;                                     where (car x) = (car y)
;;   (check-next xs ys) == #f, where (car x) != (car y)
;;                                     

(define check-next (xs ys)
    (if (null? xs)
        #t
        (if (null? ys)
            #f
            (if (= (car xs) (car ys))
                (check-next (cdr xs) (cdr ys))
                #f))))

(check-assert (check-next '(1 2) '(1 2 3)))
(check-assert (not (check-next '(1 4) '(1 2 3))))

;; (inner-loop xs ys) checks if car xs equals car ys. If so, it calls check-next
;;                    if not, it calls itself to check the next element of ys.

;; laws:
;;   (inner-loop xs ys) == #t, where xs is null
;;   (inner-loop xs ys) == #f, where ys is null
;;   (inner-loop xs ys) == (check-next (cdr xs) (cdr ys)),
;;                                     where (car x) = (car y)
;;   (inner-loop xs ys) == (inner-loop xs (cdr ys)),
;;                                     where (car x) != (car y)

(define inner-loop (xs ys)
    (if (null? xs)
        #t
        (if (null? ys)
            #f
            (if (= (car xs) (car ys))
                (check-next (cdr xs) (cdr ys))
                (inner-loop xs (cdr ys))))))


(check-assert (inner-loop '(1 2) '(1 2 3)))
(check-assert (not (inner-loop '(1 4) '(1 2 3))))

;; (contig-sublist? xs ys) checks if xs is a sublist of ys

(define contig-sublist? (xs ys)
    (if (null? xs)
        #t
        (if (= #t (inner-loop xs ys))
            #t
            #f)))

        (check-assert (contig-sublist? '(b c) '(a b c)))
        (check-assert (not (contig-sublist? '(b a) '(a b c))))
        (check-assert (not (contig-sublist? '(1 2 3 4) '(1 2 3))))
        (check-assert (not (contig-sublist? '(56) '(1 2 3))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise 8

;; (make-list xs ys) recurses through xs and adds each element to a list ys

;; laws:
;;  (make-list '() ys) == ys
;;  (make-list xs ys) == (make-list (cdr xs) (cons (car xs) ys)), where xs =
;;                        list of s-expressions with no lists
;;  (make-list xs ys) == (make-list (cdr xs) (cons (make-list (car xs) '()) ys))
;;                       where car xs = a list

(define make-list (xs ys)
    (if (null? xs)
        ys
        (if (pair? (car xs))
            (make-list (cdr xs) (cons (make-list (car xs) '()) ys))
            (make-list (cdr xs) (cons (car xs) ys)))))

        (check-expect (make-list '(1 2 3) '()) '(3 2 1))
        (check-expect (make-list '(1 2 (4 5) 3) '()) '(3 (5 4) 2 1))

;; (mirror xs) returns a list in which every lists in xs is recursively mirrored
;;             and the resulting lists are in reverse order

;; laws:
;;   (mirror '()) == '()
;;   (mirror xs) == (make-list xs '())


(define mirror (xs)
    (if (null? xs)
        '()
        (make-list xs '())))

        (check-expect (mirror '(1 2 3)) '(3 2 1))
        (check-expect (mirror '(1 2 (4 5) 3)) '(3 (5 4) 2 1))
    

;; (flatten xs) consumes a list of s-expressions and erases internal brackets

;; laws:
;;   (flatten '()) == '()
;;   (flatten a) == (list1 a), where a is an atom and a is not '()
;;   (flatten (cons x xs)) == (append (flatten x) (flatten xs))

(define flatten (xs)
    (if (null? xs)
        '()
        (if (pair? xs)
            (append (flatten (car xs)) (flatten (cdr xs)))
            (list1 xs))))

        (check-expect (flatten '(1 2 (3 4 5) (6) 7)) '(1 2 3 4 5 6 7))
        (check-expect (flatten '(1 2 3)) '(1 2 3))
        (check-expect (flatten '(((a)))) '(a))
        (check-expect (flatten '((1 a) (2 b) (3 c))) '(1 a 2 b 3 c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise 31

;; (takewhile p? xs) takes a predicate and a list and returns the longest prefix
;; of the list in which every element satisfies the predicate

;; laws:
;;   (takewhile p? '()) == '()
;;   (takewhile p? xs) == (cons (car xs) (takewhile p? (cdr xs))), where
;;                                                     (p? (car xs)) = #t
;;   (takewhile p? xs) == '(), where (p? (car xs)) = #f

(define even? (x) (= (mod x 2) 0))

(define takewhile (p? xs)
    (if (null? xs)
        '()
        (if (p? (car xs))
            (cons (car xs) (takewhile p? (cdr xs)))
            '())))

        (check-expect (takewhile even? '(2 4 6 7 8)) '(2 4 6))
        (check-expect (takewhile even? '(1 5 2 4)) '())


;; (dropwhile p? xs) removes the longest prefix and returns whatever is left
;;                   over

;; laws:
;;   (dropwhile p? '()) == '()
;;   (dropwhile p? xs) == (dropwhile p? (cdr xs)), where (p? (car xs)) = #t
;;   (dropwhile p? xs) == (cons (car xs) (cdr xs)), where (p? (car xs)) = #f

(define dropwhile (p? xs)
    (if (null? xs)
        '()
        (if (p? (car xs))
            (dropwhile p? (cdr xs))
            (cons (car xs) (cdr xs)))))

        (check-expect (dropwhile even? '(2 4 6 7 8)) '(7 8))
        (check-expect (dropwhile even? '(1 5 2 4)) '(1 5 2 4))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise B


;; (take n xs) returns the longest prefix of xs that takes at most n elements

;; laws:
;;   (take n '()) == '()
;;   (take n xs) == (cons (car xs) (take (- n 1) (cdr xs)))
;;   (take 0 xs) == '()

(define take (n xs)
    (if (null? xs)
        '()
        (if (= n 0)
            '()
            (cons (car xs) (take (- n 1) (cdr xs))))))

        (check-expect (take 4 '(1 2 3 4 5)) '(1 2 3 4))
        (check-expect (take 4 '(1 2 3)) '(1 2 3))
        (check-expect (take 0 '(1 2 3 4 5)) '())


;; (drop n xs) removes n elements form the front of the list

;; laws:
;;   (drop n '()) == '()
;;   (drop n xs) == (drop (- n 1) (cdr xs)))
;;   (drop 0 xs) == (cons (car xs) (cdr xs))

(define drop (n xs)
    (if (null? xs)
        '()
        (if (= n 0)
            (cons (car xs) (cdr xs))
            (drop (- n 1) (cdr xs)))))

        (check-expect (drop 4 '(1 2 3 4 5)) '(5))
        (check-expect (drop 0 '(1 2 3)) '(1 2 3))
        (check-expect (drop 5 '(1 2 3 4 5)) '())



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise C

;; (zip xs ys) converts a pair of lists to a list of pairs

;; laws:
;;   (zip xs ys) == '(), where either xs or ys is null
;;   (zip xs ys) == (cons (cons (car xs) (cons (car ys) '()))
;;                                                      (zip (cdr xs) (cdr ys))

(define zip (xs ys)
    (if (null? xs)
        '()
        (if (null? ys)
            '()
            (cons (cons (car xs) (cons (car ys) '()))
                                                    (zip (cdr xs) (cdr ys))))))
    
        (check-expect (zip '(1 2 3) '(a b c)) '((1 a) (2 b) (3 c)))
        (check-expect (zip '(1 2 3 4) '(a b c)) '((1 a) (2 b) (3 c)))

;; length (xs n) returns the length of a list

;; laws:
;;    (length '() n) == n
;;    (length xs n) == (length (cdr xs) (+ 1 n))

(define length (xs n)
    (if (null? (cdr xs))
        n
        (length (cdr xs) (+ 1 n))))

(check-expect (length '(1 2 3) 1) 3)
(check-expect (length '(1) 1) 1)

;; (pair-to-list ps n) reorganizes a list so that the odd elements are in the
;;                     front and the even elements are appended

;; laws:
;;  pair-to-list (ps n) == (cons (car ps) '()), where (cdr ps) is null
;;  pair-to-list (ps n) == (cons (car ps) (pair-to-list (cdr ps) (+ 1 n))),
;;                                      where (n mod 2) = 1
;;  pair-to-list (ps n) == (cons (pair-to-list (cdr ps) (+ 1 n)) (car ps))),
;;                                      where (n mod 2) = 0
(define pair-to-list (ps n)
    (if (null? (cdr ps))
        (cons (car ps) '())
        (if (= (mod n 2) 1)
            (cons (car ps) (pair-to-list (cdr ps) (+ 1 n)))
            (cons (pair-to-list (cdr ps) (+ 1 n)) (car ps)))))

    (check-expect (pair-to-list '((1 a) (2 b)) 0) '(((2 b)) 1 a))

;; (unzip ps) converts a list of pairs to a pair of lists

(define unzip (ps)
    (if (null? ps)
        '()
        (cons (take (/ (length (flatten (pair-to-list (flatten ps) 1)) 1) 2)
                                        (flatten (pair-to-list (flatten ps) 1)))
          (cons (mirror (drop (/ (length (flatten (pair-to-list (flatten ps) 1))
                                         1) 2) (flatten (pair-to-list
                                                                    (flatten ps)
                                                                    1))))'()))))

(check-expect (unzip '((1 a) (2 b) (3 c))) '((1 2 3) (a b c)))
(check-expect (unzip '((1 2) (3 4) (5 6) (7 8))) '((1 3 5 7) (2 4 6 8)))
(check-expect (unzip '()) '())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise D

;; (square a) squares a number -- only used in check-expects
(define square (a) (* a a))

;; (apply-f f xs) applies function f to the list and returns a list of results

;; laws:
;; (apply-f f '() z) == z
;; (apply-f f xs z) == (if (> (f (car xs)) (f z)), (apply-f f (cdr xs) (car xs))
;;                                              else (apply-f f (cdr xs) z)

(define apply-f (f xs z)
    (if (null? xs)
        z
        (if (> (f (car xs)) (f z))
            (apply-f f (cdr xs) (car xs))
            (apply-f f (cdr xs) z))))

(check-expect (apply-f square '(1 2 3) 1) 3)
(check-expect (apply-f square '(2 4 10) 2) 10)

;; (arg-max f xs) returns the element in xs for which (f x) is as large as
;;                possible

;; laws:
;;   (arg-max f '()) == '()
;;   (arg-max f xs) == (apply-f f xs (car xs))), where xs is a list
;;   (arg-max f xs) == (apply-f f xs xs)), where xs isn't a list

(define arg-max (f xs)
    (if (null? xs)
        '()
        (if (pair? xs)
            (apply-f f xs (car xs))
            (apply-f f xs xs))))
        

    (check-expect (arg-max square '(5 4 3 2 1)) 5)
    (check-expect (arg-max square '(6 9 3 10)) 10)
    (check-expect (arg-max car '((105 PL) (160 Algorithms) (170 Theory)))
                                                                  '(170 Theory))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise E

(record point [x y])

;; (rightmost-point ps) returns the point with the largest x coordinate

(define rightmost-point (ps)
    (arg-max car ps))

(check-expect (rightmost-point '((1 2) (2 2) (3 1))) '(3 1))
(check-expect (rightmost-point '((1 2) (2 2) (3 1))) '(3 1))
(check-expect (rightmost-point '((45 21) (42 2) (35 100))) '(45 21))