#!r6rs

;; TODO:
;; - get back variable names instead of *, build lambda
;; - for self-matches, don't both compare subtree A to B and B to A, only one direction
;; - compress original expr using abstraction
;;   (in all places, not only the two that were used to find the abstraction)

(import (except (rnrs) string-hash string-ci-hash)
        (only (ikarus) set-car! set-cdr!)
        (_srfi :1)
        (_srfi :69)
        (church readable-scheme))

;; look up value for key in alist; if not found,
;; set (default-thunk) as value and return it
(define (get/make-alist-entry alist alist-set! key default-thunk)
  (let ([binding (assq key alist)])
    (if binding
        (rest binding)
        (let* ([default-val (default-thunk)])
          (alist-set! key default-val)
          default-val))))


;; unique readable symbols. this is used to enumerate lists and to
;; generate readable variable names.
(define symbol-indizes '())

(define (get-symbol-index-container tag)
  (get/make-alist-entry symbol-indizes
                        (lambda (k v) (set! symbol-indizes (pair (pair k v) symbol-indizes)))
                        tag
                        (lambda () (list 0))))

(define (get-symbol-index tag)
  (first (get-symbol-index-container tag)))

(define (inc-symbol-index! tag)
  (let ([tag-index-container (get-symbol-index-container tag)])
    (set-car! tag-index-container (+ (first tag-index-container) 1))))

(define (sym tag)
  (inc-symbol-index! tag)
  (string->symbol (string-append (symbol->string tag)
                                 (number->string (get-symbol-index tag)))))


;; memoization
(define memtables '())

(define (get/make-memtable f)
  (get/make-alist-entry memtables
                        (lambda (k v) (set! memtables (pair (pair k v) memtables)))
                        f
                        (lambda () (make-hash-table equal?))))

(define (mem f)
  (lambda args
    (let ([mt (get/make-memtable f)])
      (hash-table-ref mt
                      args
                      (lambda () (let ([val (apply f args)])
                              (hash-table-set! mt args val)
                              val))))))


;; helper functions for accessing enumerated tree
(define etree->id first)
(define etree->tree cdr) ;; non-recursive
(define etree->children cddr)

;; transforms a tree like
;; (a (b) (c (d)) (e (f)))
;; into an enumerated tree like
;; ($1 a ($2 b) ($3 c (4 d)) ($5 e ($6 f)))
(define (enumerate-tree t)
  (if (symbol? t)
      t
      (pair (sym '$) (map enumerate-tree t))))

;; list all (enumerated) subtrees
(define (all-subtrees t)
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
(define anti-unify
  (mem (lambda (et1 et2 ignore-id-matches)
         (begin 
           (define variables '())
           (define (add-variable!)
             (begin 
               (set! variables (pair (sym 'x) variables))
               (first variables)))
           (define (build-pattern et1 et2 ignore-id-matches)
             (cond [(and (symbol? et1) (symbol? et2)) (if (eq? et1 et2) et1 (add-variable!))]
                   [(or (symbol? et1) (symbol? et2)) (add-variable!)]
                   [(and ignore-id-matches (eqv? (etree->id et1) (etree->id et2))) #f]
                   [(not (eqv? (length et1) (length et2))) (add-variable!)]
                   [else
                    (let ([unified-tree (map (lambda (t1 t2) (build-pattern t1 t2 ignore-id-matches))
                                             (etree->tree et1) (etree->tree et2))])
                      (if (any (lambda (st) (eq? st #f)) unified-tree)
                          #f
                          unified-tree))]))
           (let ((pattern (build-pattern et1 et2 ignore-id-matches)))
             (list variables pattern))))))


;; filters out a few uninteresting results (singleton, *, and tree of
;; only *s)
(define (filtered-anti-unify et1 et2 ignore-id-matches)
  (let* ([variables-pattern (anti-unify et1 et2 ignore-id-matches)]
        [variables (first variables-pattern)]
        [pattern (second variables-pattern)])
    (begin
      (if (or (member pattern variables)
              (singleton? pattern))
          #f
          variables-pattern))))

;; anti-unify all combinations of subtrees
(define (common-subtrees et1 et2 ignore-id-matches)
  (let ([sts1 (all-subtrees et1)]
        [sts2 (all-subtrees et2)])
    (apply append
           (map (lambda (st1)
                  (map (lambda (st2)
                         (list st1 st2 (filtered-anti-unify st1 st2 ignore-id-matches)))
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
  (let* ([test-tree '(((u) b y (a (b (c d e)) f g) x (a c))
                      ((i) b z (a (b (c d e)) f g) x (a d)) f)]
         [enum-test-tree (enumerate-tree test-tree)])
    (for-each display
              (list "test-tree: " test-tree "\n"
                    "enumerated test-tree: " enum-test-tree "\n\n"))
    (map pretty-print-match
         (filter (lambda (m) (third m))
                 (self-matches enum-test-tree)))))

(test)

