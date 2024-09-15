;; minimal Turing machine DSL.
;; TODO: compile transition functions.

(define-syntax define-who
  (lambda (x)
    (syntax-case x ()
      [(k name defn ... expr)
       (with-syntax ([who (datum->syntax-object #'k 'who)])
         #'(define name
             (let ([who 'name])
               defn ...
               expr)))])))

(define format-error
  (lambda (who msg . args)
    (call/cc
      (lambda (k)
        (raise (condition
                 (make-error)
                 (make-who-condition who)
                 (make-message-condition msg)
                 (make-irritants-condition args)
                 (make-format-condition)
                 (make-continuation-condition k)))))))

(define-record-type machine
  (fields
    rule
    (mutable state)
    (mutable cursor)
    tape))

(define full-state
  (lambda (state cursor tape)
    (cons state
      (map vector-ref tape cursor))))

(define-who get-transition
  (lambda (rule-set full-state)
    (let ([state (car full-state)]
          [symbol (cdr full-state)])
      (let ([tree (hashtable-ref rule-set state '())])
        (letrec ([subtree
                   (lambda (tree key)
                     (cond
                       [(null? tree) (format-error who "no transition found for ~s." full-state)]
                       [(eq? (car (car tree)) key) (cdr (car tree))]
                       [else (subtree (cdr tree) key)]))]
                 [find
                   (lambda (tree key)
                     (cond
                       [(null? key) tree]
                       [else (find
                               (subtree tree (car key))
                               (cdr key))]))])
          (find tree symbol))))))

(define split
  (lambda (l n)
    (let loop ([f '()] [e l] [i 0])
      (cond [(= i n) (values (reverse f) e)]
            [else (let ([a (car e)])
                    (loop (cons a f) (cdr e) (+ i 1)))]))))

(define-who transite
  (lambda (transition cursor tape)
    (let ([ntape (length cursor)])
      (let ([state (car transition)])
        (let-values ([(write move) (split (cdr transition) (- ntape 1))])
          (for-each vector-set! (cdr tape) (cdr cursor) write)
          (values state
                  (map
                    (lambda (x d)
                      (case d
                        ((L) (let ([x^ (- x 1)])
                               (if (< x^ 0)
                                   (format-error who "cursor moved beyond 0.")
                                   x^)))
                        ((R) (+ x 1))
                        (else x)))
                    cursor move)))))))

(define add-transition
  (lambda (rule-set state symbol transition)
    (letrec ([add-tree
               (lambda (tree key)
                 (cond
                   [(null? key) transition]
                   [(null? tree) (cons
                                   (cons (car key) (add-tree '() (cdr key)))
                                   '())]
                   [(eq? (car (car tree)) (car key))
                    (cons
                      (cons (car key) (add-tree (cdr (car tree)) (cdr key)))
                      (cdr tree))]
                   [else (cons (car tree) (add-tree (cdr tree) key))]))])
      (hashtable-update! rule-set state
        (lambda (tree) (add-tree tree symbol))
        '()))))

(define expand-rule
  (lambda (bind rule)
    (letrec ([expand
               (lambda (rule env)
                 (cond
                   [(null? rule) '(())]
                   [(assq (car rule) env) =>
                    (lambda (entry)
                      (expand (cons (cdr entry) (cdr rule)) env))]
                   [(assq (car rule) bind) =>
                    (lambda (entry)
                      (let ([var (car entry)]
                            [range (cadr entry)])
                        (apply append
                          (map
                            (lambda (x)
                              (expand
                                (cons x (cdr rule))
                                (cons (cons var x) env)))
                            range))))]
                   [else (let ([sym (car rule)])
                           (map
                             (lambda (r) (cons sym r))
                             (expand (cdr rule) env)))]))])
      (expand rule '()))))

(define run
  (lambda (machine)
    (let ([rule (machine-rule machine)]
          [tape (machine-tape machine)])
      (let loop ([state (machine-state machine)]
                 [cursor (machine-cursor machine)])
        (if (eq? state 'halt)
            (begin
              (machine-state-set! machine 'halt)
              (machine-cursor-set! machine cursor)
              machine)
            (let-values ([(state^ cursor^)
                          (transite
                            (get-transition rule (full-state state cursor tape))
                            cursor tape)])
              (loop state^ cursor^)))))))

(define step
  (lambda (machine)
    (let ([rule (machine-rule machine)]
          [tape (machine-tape machine)]
          [state (machine-state machine)]
          [cursor (machine-cursor machine)])
      (let-values ([(state^ cursor^)
                    (transite
                      (get-transition rule (full-state state cursor tape))
                      cursor tape)])
        (machine-state-set! machine state^)
        (machine-cursor-set! machine cursor^)
        machine))))

(define set-input
  (lambda (machine input)
    (let ([input-tape (car (machine-tape machine))]
          [work-tape (cdr (machine-tape machine))])
      (let ([init
              (lambda (tape)
                (vector-fill! tape '-)
                (vector-set! tape 0 '>))])
        (machine-state-set! machine 'start)
        (machine-cursor-set! machine (make-list (+ 1 (length work-tape)) 1))
        (init input-tape)
        (for-each init work-tape)
        (let loop ([i 1] [input input])
          (unless (null? input)
            (vector-set! input-tape i (car input))
            (loop (+ i 1) (cdr input))))))))

(define do-make-turing-machine
  (lambda (tape-length ntapes rules)
    (let* ([h (make-eq-hashtable)]
           [machine (make-machine h #f #f
                      (let loop ([i 0])
                        (if (= i ntapes) '()
                            (cons (make-vector tape-length) (loop (+ i 1))))))])
      (for-each
        (lambda (rule)
          (let-values ([(condition operation) (split rule (+ ntapes 1))])
            (add-transition h
              (car condition)
              (cdr condition)
              operation)))
        rules)
      machine)))

(define-syntax make-turing-machine
  (syntax-rules ()
    [(_ tape-length bind rule ...)
     (let ([rules
             (map
               (lambda (ll) (append (car ll) (cadr ll)))
               (quote (rule ...)))])
       (do-make-turing-machine
         tape-length
         (div (- (length (car rules)) 1) 3)
         (apply append
           (map
             (lambda (r)
               (expand-rule (quote bind) r))
             rules))))]))

(record-writer (type-descriptor machine)
  (lambda (m p wr)
    (wr (machine-state m) p)
    (display-string "\n" p)
    (for-each
      (lambda (c t)
        (let ([n (vector-length t)])
          (let ([last
                  (let loop ([i (- n 1)])
                    (cond [(= i 0) 0]
                          [(not (eq? (vector-ref t i) '-)) i]
                          [else (loop (- i 1))]))])
            (let loop ([i 0])
              (cond [(= i n) (void)]
                    [(and (> i (+ last 3))
                          (> i (+ c 3)))
                     (display-string "..." p)]
                    [(= i c)
                     (display-string "[" p)
                     (wr (vector-ref t i) p)
                     (display-string "]" p)
                     (display-string " " p)
                     (loop (+ i 1))]
                    [else
                      (wr (vector-ref t i) p)
                      (display-string " " p)
                      (loop (+ i 1))])))
          (display-string "\n" p)))
      (machine-cursor m)
      (machine-tape m))))

(define boring
  (make-turing-machine 10
    ([i (0 1)])
    ((start - -) (rev - L L))
    ((start 0 -) (start 1 R R))
    ((start 1 -) (start 0 R R))
    ((rev i 0)   (rev 1 L L))
    ((rev i 1)   (rev 0 L L))
    ((rev > >)   (halt start S S))))

(define mult
  (make-turing-machine 50000

    ([i (0 1)]
     [j (0 1)]
     [x (0 1 > -)]
     [y (0 1 > -)])

    ((start i - - -) (start - - - R S S S))
    ((start - - - -) (copy - - - R S S S))

    ((copy i - - -) (copy i - - R R S S))
    ((copy - - - -) (back - - - L L S S))

    ((back i j - -) (back j - - L L S S))
    ((back x > - -) (back > - - L S S S))
    ((back > > - -) (maybe > - - R R S S))

    ((maybe i 0 - x) (maybe 0 - x S R R R))
    ((maybe i 1 - x) (place 1 - x S S S S))
    ((maybe i - - x) (0 - - x S S S S))

    ((place i 1 - x) (place 1 i x R S R S))
    ((place - 1 - x) (reset 1 - x L S L S))

    ((reset i 1 j x) (reset 1 j x L S L S))
    ((reset > 1 x y) (add 1 x y R S R S))

    ((add i 1 0 -) (add 1 0 0 S S R R))
    ((add i 1 0 0) (add 1 0 0 S S R R))
    ((add i 1 0 1) (add 1 0 1 S S R R))
    ((add i 1 1 -) (add 1 1 1 S S R R))
    ((add i 1 1 0) (add 1 1 1 S S R R))
    ((add i 1 1 1) (carry 1 1 0 S S R R))
    ((add i 1 - x) (clean 1 - x S S L L))

    ((carry i 1 0 -) (add 1 0 1 S S R R))
    ((carry i 1 0 0) (add 1 0 1 S S R R))
    ((carry i 1 0 1) (carry 1 0 0 S S R R))
    ((carry i 1 1 -) (carry 1 1 0 S S R R))
    ((carry i 1 1 0) (carry 1 1 0 S S R R))
    ((carry i 1 1 1) (carry 1 1 1 S S R R))
    ((carry i 1 - -) (clean 1 - 1 S S L L))
    ((carry i 1 - 0) (carry 1 - 1 S S L L))
    ((carry i 1 - 1) (carry 1 0 0 S S R R))

    ((clean i 1 j x) (clean 1 - x S S L L))
    ((clean i 1 - x) (next 1 - x S S R R))
    ((clean i 1 > x) (next 1 > x S S R R))
    ((next i 1 - x)  (maybe 1 - x S R R R))

    ((0 i - - j) (0 - - j S S S L))
    ((0 i - - -) (0 - - 0 S S S L))
    ((0 i - - >) (halt - - > S S S S))))
