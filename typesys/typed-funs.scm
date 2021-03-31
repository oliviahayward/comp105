(define (array int) drop ([n : int] [xs : (array int)])
    (if (null? xs)
        '()
        (if (= n 0)
            (cons (car xs) (cdr xs))
            (drop (- n 1) (cdr xs)))))

(check-type drop (int (array int) -> (array int)))