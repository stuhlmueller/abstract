#!r6rs
;;TODO:
;;- figure out a good way to test a library w/o exporting all the functions

(import (pi abstract)
        (srfi :78 lightweight-testing)
        (_srfi :1))

;;bug when compressing the following 
(define test-data '(let () (begin (let () (define F1 (lambda (V1) (set-pixel! i V1 4 1))) (begin (F1 3) (F1 4) (F1 5) (F1 6) (F1 7))) (let () (define F1 (lambda (V1) (set-pixel! i V1 4 1))) (begin (F1 15) (F1 14) (F1 13) (F1 12) (F1 11))) (let () (define F1 (lambda (V1) (set-pixel! i V1 4 1))) (begin (F1 21) (F1 19) (F1 20) (F1 17) (F1 18))))))

;;(define test-data '(let () (begin (let () (define F1 (lambda (V1) (set-pixel! i V1 4 1))) (begin (F1 3) (F1 4))) (let () (define F1 (lambda (V1) (set-pixel! i V1 4 1))) (begin (F1 15) (F1 14))))))



(define program-form (sexpr->program test-data))

(pretty-print (map program->sexpr (compressions program-form)))
(exit)
;;;abstraction-proposer tests
;;(define test-expr '(let () #t))
;;(define test-expr '(let () (if (if #t #t #t) (if #t #t #t) (if #t #t #t))))

;;test for making sure abstraction names don't conflict with names existing in the data being compressed
;; (define test-expr '(let () (define F1 (lambda () #t)) (or (and (F1) (F1) (F1)) (and (F1) (F1) (F1)) (and (F1) (F1) (F1)))))
;; (define program-form (sexpr->program test-expr))

;;(pretty-print (abstraction-move test-expr))
;;(define test-expr1 (abstraction-move test-expr))
;;(pretty-print (list "texp" (first test-expr1)))
;;make sure the output of abstraction-proposer is an sexpr of the right form, use match library

;;(pretty-print (compressions program-form))


;; ;;(pretty-print (beam-compression '((a b c) (a b c) (a b c) (a b c)) 2))

;; ;;(pretty-print (beam-compression '(f (f (f (f (f (f (f (f a)))))))) 2))

;; (define p '(let () (define (g x) x) (define (h) (+ 1 2)) (g (g))))

;; ;; (define a (make-abstraction '(X b Y) '(X Y)))
;; ;; (pretty-print a)
;; ;; (pretty-print (abstraction->define a))
;; ;; (pretty-print (define->abstraction (abstraction->define a)))

;; ;; (pretty-print (get-abstractions p))

;; (pretty-print (sexpr->program '(let () (define (f x) (+ 2 2)) (f 3))))

;; (pretty-print (sexpr->program '(let ()   (f 3))))

;; (pretty-print (sexpr->program p))
;; (define (test-proposal)
;;   (let ([init (make-program '() '(+ (+ (+ a a a) (+ c c c) (+ d d d)) (f (f (f (f (f (f (f (f (f (f (f (+ a a a)))))))))))) (+ a a a)))])
;;     (define (random-walk steps program)
;;       (let* ([proposed (proposal program)]
;;              [next-program (first proposed)])
;;         (pretty-print proposed)
;;         (if (= 0 steps)
;;             program
;;             (random-walk (- steps 1) next-program))))
;;     (random-walk 10 init)))


;; (define (test-abstraction-proposer)
;;   (let ([init '(let () (+ (+ (+ a a a) (+ c c c) (+ d d d)) (f (f (f (f (f (f (f (f (f (f (f (+ a a a)))))))))))) (+ a a a)))])
;;     (define (random-walk steps sexpr)
;;       (let* ([proposed (abstraction-proposer sexpr)]
;;              [next-program (first proposed)])
;;         (pretty-print proposed)
;;         (if (= 0 steps)
;;             sexpr
;;             (random-walk (- steps 1) next-program))))
;;     (random-walk 10 init)))

;; ;;(let () (+ 2 3)


;; (test-abstraction-proposer)
;; ;;(test-proposal)

;; ;; (define (test-unify)
;; ;;   (let* ([sexpr '(a b c d)]
;; ;;          [pattern '(A b c A)] 
;; ;;          [variables '(A B)]) 
;; ;;     (pretty-print (unify sexpr pattern variables))))

;; ;; ;;((A . a)) correct output?!
;; ;; (define (test-self-matching)
;; ;;   (let* ([test-tree '(((u) b y (a (b (c d e)) f g) x (a c))
;; ;;                       ((i) b z (a (b (c d e)) f g) x (a d)) f)]
;; ;;          [enum-test-tree (enumerate-tree test-tree)])
;; ;;     (for-each display
;; ;;               (list "test-tree: " test-tree "\n"
;; ;;                     "enumerated test-tree: " enum-test-tree "\n\n"))
;; ;;     (map pretty-print-match
;; ;;          (filter (lambda (m) (third m))
;; ;;                  (self-matches enum-test-tree)))))

;; ;; (define (test-match-replacement)
;; ;;   (let* ([test-tree '(e f ((d (a b c)) b c) g h (e f (q q)))]
;; ;;          [abstraction (make-abstraction '(X b Y) '(X Y))]
;; ;;          [abstraction2 (make-abstraction '(e f Z) '(Z))])
;; ;;     (pretty-print (replace-matches test-tree abstraction))
;; ;;     (pretty-print (replace-matches test-tree abstraction2))))

;; ;; (define (test-compression sexpr)
;; ;;   (for-each display (list "original expr:\n" sexpr "\n"
;; ;;                           "size: " (size sexpr)
;; ;;                           "\n\n"
;; ;;                           "compressed exprs:\n"))
;; ;;   (map pretty-print-program
;; ;;        (sort-by-size
;; ;;         (unique-programs
;; ;;          (beam-search-compressions 10 (make-program '() sexpr))))))

;; ;; (define (test-redundant-variables)
;; ;;   (let* ([tabs (make-abstraction '(+ A B C D) '(A B C D))]
;; ;;          [test-trees '((+ a b b a) (+ q d d q) (+ f m m f))])
;; ;;     ;;         [test-trees '((+ 2 3 3 2) (+ 4 5 5 4) (+ 6 1 1 6))])
;; ;;     (map (lambda (x) (replace-matches x tabs)) test-trees)
;; ;;     (pretty-print test-trees)    
;; ;;     (pretty-print tabs)
;; ;;     (pretty-print (remove-redundant-variables tabs))))


;; ;; ;; the expression should have a pattern with repeated variables
;; ;; (define (test-repeated-variable-pattern)
;; ;;   (let* ([expr '(+ (+ a b a) (+ c d c))]
;; ;;          [et (enumerate-tree expr)])
;; ;;     (pretty-print (self-matches et))))

;; ;; (define (test-capture-vars)
;; ;;   (pretty-print (capture-vars (make-abstraction '(v1 v2 (f a v3)) '(v3)))))

;; ;; ;; (test-capture-vars)


;; ;; (define (test-instantiate-pattern)
;; ;;   (let ([abstraction (make-named-abstraction 'F '(+ a a (+ b c)) '(a c))]
;; ;;         [sexpr '(F 3 4)])
;; ;; ;;    (pretty-print (replace-var (abstraction->pattern abstraction) '(a 3)))))
;; ;;     (pretty-print (instantiate-pattern sexpr abstraction))))

;; ;; (define (test-inline)
;; ;;   (let* ([a1 (make-named-abstraction 'F '(+ a (G 99 100) (+ b c)) '(a c))]
;; ;;          [a2 (make-named-abstraction 'G '(* (F 2 1) (+ q q) c a) '(a c))]
;; ;;          [body '(+ (F 3 4) (* (G (F 20 30) 8) (G 9 10)))]
;; ;;          [program (make-program (list a1 a2) body)])
;; ;;     (pretty-print (inline program .5))))

        
;; ;; ;;(test-inline)
;; ;; ;;(recursive? '(f (f x)))
;; ;; ;;(test-compression '((f (f (f (f x)))) (f (f (f (f x)))) (f (f (f (f x)))) (g (f (f (f x))))))
;; ;; ;; (test-repeated-variable-pattern)
;; ;; ;; (test-compression '((f (f (f (f (f (f (f (f (f (f (f (f x))))))))))))))
;; ;; ;;(test-compression '((h (m (h (m (h (m (h (m (c))))))))) (h (m (h (m (h (m (c))))))) (h (m (h (m (c))))) (h (m (c))) (f (f (f (f (f (f (f (f (f (f (f (f x))))))))))))))
;; ;; ;; (test-compression '(f (a x) (f (a x) (f (a x) b (a x)) (a x)) (a x)))
;; ;; ;; (test-compression '(f (a b (x y (u k l)))
;; ;; ;;                       (a b c)
;; ;; ;;                       (a b (z d (u k l)))
;; ;; ;;                       (a b c)))
;; ;; ;; (test-compression '(a (a (foo bar) b) (a (bar foo) b) (a (bzar fzoo) b)))
;; ;; ;;(test-compression '(f (a x) (f (a x) (f (a x) b (a x)) (a x)) (a x)))
;; ;; ;; (test-compression '(k (h (g (f (a b (x y (u k l)))
;; ;; ;;                               (a b c)
;; ;; ;;                               (a b (z d (u k l)))
;; ;; ;;                               (a b c))
;; ;; ;;                            (f (a b (x y (u k l)))
;; ;; ;;                               (a b c)
;; ;; ;;                               (a b (z d (u k l)))
;; ;; ;;                               (a b c)))
;; ;; ;;                         (g (f (a b (x y (u k l)))
;; ;; ;;                               (a b c)
;; ;; ;;                               (a b (z d (u k l)))
;; ;; ;;                               (a b c))
;; ;; ;;                            (f (a b (x y (u k l)))
;; ;; ;;                               (a b c)
;; ;; ;;                               (a b (z d (u k l)))
;; ;; ;;                               (a b c))))
;; ;; ;;                      (h (g (f (a b (x y (u k l)))
;; ;; ;;                               (a b c)
;; ;; ;;                               (a b (z d (u k l)))
;; ;; ;;                               (a b c))
;; ;; ;;                            (f (a b (x y (u k l)))
;; ;; ;;                               (a b c)
;; ;; ;;                               (a b (z d (u k l)))
;; ;; ;;                               (a b c)))
;; ;; ;;                         (g (f (a b (x y (u k l)))
;; ;; ;;                               (a b c)
;; ;; ;;                               (a b (z d (u k l)))
;; ;; ;;                               (a b c))
;; ;; ;;                            (f (a b (x y (u k l)))
;; ;; ;;                               (a b c)
;; ;; ;;                               (a b (z d (u k l)))
;; ;; ;;                               (a b c))))))

;; ;; ;;(test-compression '((f (f (f (f x)))) (g (g (g (g x))))))

;; ;; (define (test-proposal)
;; ;;   (let ([init (make-program '() '(+ (+ (+ a a a) (+ c c c) (+ d d d)) (f (f (f (f (f (f (f (f (f (f (f (+ a a a)))))))))))) (+ a a a)))])
;; ;;     (define (random-walk steps program)
;; ;;       (let* ([proposed (proposal program)]
;; ;;              [next-program (first proposed)])
;; ;;         (pretty-print proposed)
;; ;;         (if (= 0 steps)
;; ;;             program
;; ;;             (random-walk (- steps 1) next-program))))
;; ;;     (random-walk 10 init)))

;; ;; (test-proposal)
;; ;; ;;(test-inline)

;; ;; (define (test-recursion-abstraction?)
;; ;;   (let ([r (make-recursion-abstraction '(f 0))]
;; ;;         [a (make-named-abstraction 'G '(* (F 2 1) (+ q q) c a) '(a c))])
;; ;;     (pretty-print r)
;; ;;     (pretty-print (recursion-abstraction? r))
;; ;;     (pretty-print (recursion-abstraction? a))))

;; ;; ;;(test-recursion-abstraction?)

;; ;; (define (test-higher-order-inline)
;; ;;   (let* ([a1 (make-named-abstraction 'G '(* (f 3) x) '(f x))]
;; ;;          [a2 (make-named-abstraction 'F '(+ x x x) '(x))]
;; ;;          [body '(+ (G F 5) (F 84))]
;; ;;          [program (make-program (list a1 a2) body)])
;; ;;     (pretty-print (inline program .5))))
        
;; ;; ;;(test-higher-order-inline)
  
;; ;; (define (test-inline-recursion)
;; ;;   (let ([r (make-recursion-abstraction '(f 0))])
;; ;;     (pretty-print (inline-recursion r))))

;; ;; ;;(test-inline-recursion)
