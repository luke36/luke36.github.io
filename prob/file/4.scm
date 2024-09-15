(define eval
  (lambda (code*)
    (let ([ram (make-vector 100)]
          [current 50])
      (letrec ([repeat
                 (lambda (n thunk)
                   (unless (<= n 0)
                     (thunk)
                     (repeat (sub1 n) thunk)))]
               [run1
                 (lambda (code)
                   (case code
                     [+ (vector-set! ram current (add1 (vector-ref ram current)))]
                     [- (vector-set! ram current
                          (max 0 (sub1 (vector-ref ram current))))]
                     [> (set! current (add1 current))]
                     [< (set! current (max 0 (sub1 current)))]
                     [else (repeat (vector-ref ram current) (lambda () (run code)))]))]
               [run
                 (lambda (code*)
                   (cond [(null? code*) (vector-ref ram 50)]
                         [else
                           (run1 (car code*))
                           (run (cdr code*))]))])
        (vector-set! ram 50 10)
        (run code*)))))
