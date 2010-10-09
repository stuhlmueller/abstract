#!r6rs

;; TODO:
;; - for self-matches, don't both compare subtree A to B and B to A, only one direction
;; - compress original expr using abstraction
;;   (in all places, not only the two that were used to find the abstraction)

(import (except (rnrs) string-hash string-ci-hash)
        (only (ikarus) set-car! set-cdr!)
        (_srfi :1)
        (_srfi :69)
        (church readable-scheme))

(define (curry fun . args)
  (lambda x
    (apply fun (append args x))))

(define (all lst)
  (if (null? lst)
      #t
      (and (first lst)
           (all (rest lst)))))

;compute the number of nodes in a tree
(define (size tree)
  (if (list? tree)
      (+ 1 (apply + (map size tree)))
      1))
      

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


;; data structures

(define etree->id first)
(define etree->tree cdr) ;; non-recursive
(define etree->children cddr)

(define (make-abstraction pattern variables)
  (list 'abstraction (sym 'F) variables pattern))
(define abstraction->name second)
(define abstraction->vars third)
(define abstraction->pattern fourth)

;make a define statement out of an abstraction
(define (abstraction->procedure abstraction)
  (let ((name (abstraction->name abstraction))
        (variables (abstraction->vars abstraction))
        (pattern (abstraction->pattern abstraction)))
    (list 'define (pair name variables) pattern)))


;; transforms a tree like
;; (a (b) (c (d)) (e (f)))
;; into an enumerated tree like
;; ($1 a ($2 b) ($3 c (4 d)) ($5 e ($6 f)))
(define (enumerate-tree t)
  (if (symbol? t)
      t
      (pair (sym '$) (map enumerate-tree t))))

(define (unenumerate-tree t)
  (if (symbol? t)
      t
      (map unenumerate-tree (rest t))))

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
             (set! variables (pair (sym 'v) variables))
             (first variables))
           (define (build-pattern et1 et2 ignore-id-matches)
             (cond [(and (symbol? et1) (symbol? et2)) (if (eq? et1 et2) et1 (add-variable!))]
                   [(or (symbol? et1) (symbol? et2)) (add-variable!)]
                   [(and ignore-id-matches (eqv? (etree->id et1) (etree->id et2))) #f]
                   [(not (eqv? (length et1) (length et2))) (add-variable!)]
                   [else
                    (let ([unified-tree (map (lambda (t1 t2) (build-pattern t1 t2 ignore-id-matches))
                                             (etree->tree et1)
                                             (etree->tree et2))])
                      (if (any false? unified-tree)
                          #f
                          unified-tree))]))
           (let ([pattern (build-pattern et1 et2 ignore-id-matches)])
             (list variables pattern))))))

;; filter out a few uninteresting abstractions
;; (single variable or singleton list)
(define (filtered-anti-unify et1 et2 ignore-id-matches)
  (let* ([variables-pattern (anti-unify et1 et2 ignore-id-matches)]
         [variables (first variables-pattern)]
         [pattern (second variables-pattern)])
    (begin
      (define (plain-var-list? pattern)
        (all (map (lambda (i) (member i variables)) pattern)))
      (if (or (member pattern variables)
              (singleton? pattern)
              (and (list? pattern) (plain-var-list? pattern)))
          #f
          (if (false? pattern)
              #f
              (make-abstraction pattern variables))))))

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

;; takes a sexpr (s), a sexpr with variables (sv) and a proc name, e.g.
;; s = (foo (foo a b c) b c)
;; sv = (foo V b c)
;; name = P
;; first pass: (P (foo a b c))
;; second (operand) pass: (P (P a))
;; returns #f if abstraction cannot be applied, otherwise variable assignments
;; ! assumes that each variable occurs only once in sv
(define (unify s sv vars)
  (define (variable? obj)
    (member obj vars))
  (cond [(variable? sv) (list (pair sv s))]
        [(and (symbol? s) (symbol? sv)) (if (eq? s sv) '() #f)]
        [(or (symbol? s) (symbol? sv)) #f]
        [(not (eqv? (length s) (length sv))) #f]
        [else
         (let ([assignments (map (lambda (si sj) (unify si sj vars)) s sv)])
           (if (any false? assignments)
               #f
               (apply append assignments)))]))

;; doesn't deal with partial matches, could use more error checking
(define (replace-matches s abstraction)
  (let ([unified-vars (unify s
                             (abstraction->pattern abstraction)
                             (abstraction->vars abstraction))])
    (if (false? unified-vars)
        (if (list? s)
            (map (lambda (si) (replace-matches si abstraction)) s)
            s)
        (pair (abstraction->name abstraction)
              (map (lambda (var) (replace-matches (rest (assq var unified-vars)) abstraction))
                   (abstraction->vars abstraction))))))

;rewrite the expression in terms of the patterns found from self-matching, returns the compressed programs and their sizes 
(define (compressions tree)
  (let* ((etree (enumerate-tree tree))
         (valid-abstractions (get-valid-abstractions (self-matches etree)))
         (compressed-trees (map (curry compress-tree tree) valid-abstractions)))
    (zip compressed-trees (map size compressed-trees))))

;compress a tree using the given abstraction
(define (compress-tree tree abstraction)
  (let* ((proc (abstraction->procedure abstraction))
         (compression (replace-matches tree abstraction)))
    (list 'begin proc compression)))

;throw out any that are false
(define (get-valid-abstractions subtree-matches)
  (let ((abstractions (map third subtree-matches)))
    (filter (lambda (x) x) abstractions)))


(define (pretty-print-match m)
  (for-each display
            (list "t1: " (unenumerate-tree (first m)) "\n"
                  "t2: " (unenumerate-tree (second m)) "\n"
                  "m: " (abstraction->pattern (third m)) "\n\n")))

(define (test-self-matching)
  (let* ([test-tree '(((u) b y (a (b (c d e)) f g) x (a c))
                      ((i) b z (a (b (c d e)) f g) x (a d)) f)]
         [enum-test-tree (enumerate-tree test-tree)])
    (for-each display
              (list "test-tree: " test-tree "\n"
                    "enumerated test-tree: " enum-test-tree "\n\n"))
    (map pretty-print-match
         (filter (lambda (m) (third m))
                 (self-matches enum-test-tree)))))

(define (test-match-replacement)
  (let* ([test-tree '(e f ((d (a b c)) b c) g h)]
         [abstraction (make-abstraction '(X b c) '(X))])
    (pretty-print (replace-matches test-tree abstraction))))

(define (test-compression)
  (pretty-print (compressions '(f a (f a (f a b c) c) c))))

(test-compression)
;(test-self-matching)
;(test-match-replacement)
;(self-matches (enumerate-tree '(a (d e) (d e))))
;(exit)
