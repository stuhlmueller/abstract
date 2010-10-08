#!r6rs

(import (except (rnrs) string-hash string-ci-hash)
        (_srfi :1)
        (_srfi :69)
        (church readable-scheme))

;; (make-hash-table equal?)
;; (hash-table-ref ht key (lambda () default))
;; (hash-table-set! ht key val)

;; (list (func ht) ...)
;; memq

;; helper functions for accessing enumerated tree
(define etree->id first)
(define etree->tree cdr) ;; non-recursive
(define etree->children cddr)

;; transforms a tree like
;; (a (b) (c (d)) (e (f)))
;; into an enumerated tree like
;; (1 a (2 b) (3 c (4 d)) (5 e (6 f)))
(define (enumerate-tree t)
  (define ec 0)
  (define (enum t)
    (if (symbol? t)
        t
        (begin
          (set! ec (+ ec 1))
          (let ([ec2 ec])
            (pair ec2 (map enum t))))))
  (enum t))

;; list all (enumerated) subtrees
(define (all-enum-subtrees t)
  (let loop ([t (list t)])
    (cond [(null? t) '()]
          [(number? (first t)) (loop (rest t))]
          [(symbol? (first t)) (loop (rest t))]
          [else (pair (first t) (loop (append (first t) (rest t))))])))

;; is obj a list like '(x)?
(define (singleton? obj)
  (and (pair? obj)
       (symbol? (first obj))
       (null? (rest obj))))

;; recursively tests whether all values in a list are
;; equal to a given value
(define (all-val? lst val)
  (if (null? lst)
      #t
      (and (if (list? (first lst))
               (all-val? (first lst) val)
               (eq? (first lst) val))
           (all-val? (rest lst) val))))

;; returns #f if trees cannot be unified,
;; otherwise tree with * in places where they differ
;; returns for (the enumerated version of) trees
;; (z (a (x (i (j)) (h (m)))) (c) (d (f) (i)))
;; (z (a (x (k (l)) (h (m)))) (c) (d (h (f)) (i)))
;; this:
;; (z (a (x (* (*)) (h (m)))) (c) (d * (i)))
;; filters out a few uninteresting results (singleton, *, and tree of
;; only *s)
(define (anti-unify et1 et2 ignore-id-matches)
  (define (%anti-unify et1 et2)
    (cond [(and (symbol? et1) (symbol? et2)) (if (eq? et1 et2) et1 '*)]
          [(or (symbol? et1) (symbol? et2)) '*]
          [(and ignore-id-matches (eqv? (etree->id et1) (etree->id et2))) #f]
          [(not (eqv? (length et1) (length et2))) '*]
          [else
           (let ([unified-tree (map (lambda (t1 t2) (%anti-unify t1 t2))
                                    (etree->tree et1) (etree->tree et2))])
             (if (any (lambda (st) (eq? st #f)) unified-tree)
                 #f
                 unified-tree))]))
  (let ([result (%anti-unify et1 et2)])
    (if (or (eq? result '*)
            (singleton? result)
            ;; (and (list? result) (all-val? result '*))
            )
        #f
        result)))

;; anti-unify all combinations of subtrees
(define (common-subtrees et1 et2 ignore-id-matches)
  (let ([sts1 (all-enum-subtrees et1)]
        [sts2 (all-enum-subtrees et2)])
    (apply append
           (map (lambda (st1)
                  (map (lambda (st2)
                         (list st1 st2 (anti-unify st1 st2 ignore-id-matches)))
                         sts2))
                       sts1))))

;; return all subtrees that enumerated tree et has in common with
;; itself, ignore identity matches
(define (self-matches et)
  (common-subtrees et et #t))

(define (pretty-print-match m)
  (for-each display
            (list "t1: " (first m) "\n"
                  "t2: " (second m) "\n"
                  "m: " (third m) "\n\n")))

(define (test)
  (let* ([test-tree '(((u) b y x (a c))
                      ((i) b z x (a d)) f)]
         [enum-test-tree (enumerate-tree test-tree)])
    (for-each display
              (list "test-tree: " test-tree "\n"
                    "enumerated test-tree: " enum-test-tree "\n\n"))
    (map pretty-print-match
         (filter (lambda (m) (third m))
                 (self-matches enum-test-tree)))))

;; - get back variable names instead of *, build lambda
;; - mem for anti-unify
;; - for self-matches, don't both compare subtree A to B and B to A, only one direction
;; - compress original expr using abstraction
;;   (in all places, not only the two that were used to find the abstraction)
(test)

