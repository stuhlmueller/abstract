#!r6rs

;; TODO:
;; - at [1], when variables are part of a pattern, make the pattern more general
;;   such that the variables are given in the function call


(import (except (rnrs) string-hash string-ci-hash)
        (only (ikarus) set-car! set-cdr!)
        (_srfi :1)
        (_srfi :69)
;        (srfi :13)
        (church readable-scheme))

(define (all-equal? lst)
  (all (map (lambda (itm) (equal? (first lst) itm)) (rest lst))))

(define (all-assoc alist key)
  (filter (lambda (entry) (equal? (first entry) key)) alist))

(define (more-than-one lst)
  (> (length lst) 1))

(define (curry fun . const-args)
  (lambda args
    (apply fun (append const-args args))))

(define (all lst)
  (if (null? lst)
      #t
      (and (first lst)
           (all (rest lst)))))

(define (max-take lst n)
  (if (<= (length lst) n)
      lst
      (take lst n)))

;; compute the size of a program
(define (size tree)
  (if (list? tree)
      (cond [(tagged-list? tree 'begin) (size (rest tree))] ;; ignore 'begin symbol
            [(tagged-list? tree 'define) (size (cddr tree))] ;; ignore 'define symbol + args
            [else (apply + (map size tree))])
      1))

(define (sexp-replace old new sexp)
  (if (list? sexp)
      (map (curry sexp-replace old new) sexp)
      (if (equal? sexp old) new sexp)))

(define (sexp-search pred? func sexp)
  (if (list? sexp)
      (map (curry sexp-search pred? func) sexp)
      (if (pred? sexp) (func sexp) sexp)))

;; eventually use this in for self-matching of subtrees
(define (unique-commutative-pairs lst func)
  (define (recursion lst1 lst2)
    (if (null? lst2)
        '()
        (let ((from1 (first lst1)))
          (append (map (lambda (from2) (func from1 from2)) lst2)
                  (recursion (rest lst1) (rest lst2))))))
  (recursion lst (rest lst)))


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

;;language specific functions ;use reg-exps
;;temp fix b/c problems access to srfi 13
(define (var? expr)
  (if (symbol? expr)
      (let* ([var-pattern "v"]
             [string-expr (symbol->string expr)])
;        (string-prefix? var-pattern string-expr))))
        (equal? (substring string-expr 0 1) "v"))
      #f))
;; data structures & associated functions

(define etree->id first)
(define etree->tree cdr) ;; non-recursive
(define etree->children cddr)

(define (make-abstraction pattern variables)
  (make-named-abstraction (sym 'F) pattern variables))
(define (make-named-abstraction name pattern variables)
  (list 'abstraction name variables pattern))
(define abstraction->name second)
(define abstraction->vars third)
(define abstraction->pattern fourth)

;; make a define statement out of an abstraction
(define (abstraction->define abstraction)
  (let ((name (abstraction->name abstraction))
        (variables (abstraction->vars abstraction))
        (pattern (abstraction->pattern abstraction)))
    (list 'define (pair name variables) pattern)))

(define (make-program abstractions body)
  (list 'program abstractions body))
(define program->abstractions second)
(define program->body third)

(define (program->sexpr program)
  `(begin
     ,@(map abstraction->define (program->abstractions program))
     ,(program->body program)))

;; FIXME: assumes that there is only one program for each size
(define (unique-programs programs)
  (define ht (make-hash-table eqv?))
  (map (lambda (p) (hash-table-set! ht (size (program->sexpr p)) p)) programs)
  (map rest (hash-table->alist ht)))

(define (sort-by-size programs)
  (let* ([program-sizes (map (compose size program->sexpr) programs)]
         [programs-with-size (zip programs program-sizes)]
         [size< (lambda (a b) (< (second a) (second b)))])
    (map first (list-sort size< programs-with-size))))

(define (shortest-n n programs)
  (max-take (sort-by-size programs) n))


;; a history of how each pattern was used, the keys to the hashtable
;; are names of abstractions and the entries are hashtables where the
;; keys are variable names for the abstractions and the values are
;; lists of past instances
(define abstraction-instances (make-hash-table eqv?))
(define (abstraction-instances->get-instances abstraction)
  (hash-table-ref abstraction-instances (abstraction->name abstraction)))
(define (abstraction-instances->add-instance! abstraction unified-vars)
  (let* ([aname (abstraction->name abstraction)]
         [avars (abstraction->vars abstraction)]
         [abstraction-history
          (hash-table-ref
           abstraction-instances
           aname
           (lambda ()
             (let ([new-history (make-abstraction-history avars)])
               (hash-table-set! abstraction-instances aname new-history)
               new-history)))])
    (abstraction-history->add! abstraction-history unified-vars)))

;; entries into the abstraction-instances table, basically a list of
;; instances for each variable of the abstraction
(define (make-abstraction-history abstraction-vars)
  (let* ([new-history (make-hash-table eqv?)]
         [add-var! (lambda (var) (hash-table-set! new-history var '()))])
    (map add-var! abstraction-vars)
    new-history))

(define abstraction-history->var-history hash-table-ref)

;; add a new instance to an abstractions history
(define (abstraction-history->add! ahist unified-vars)
  (begin
    (define (update-var! unified-var)
      (let ([var (unified-var->var unified-var)]
            [new-instance (unified-var->instance unified-var)])
        (hash-table-update! ahist var (lambda (old-instances) (pair new-instance old-instances)))))
    (map update-var! unified-vars)))

(define unified-var->var first)
(define unified-var->instance rest)

;; remove redundant variables for an abstraction e.g. (+ 2 2) (+ 3 3)
;; gives pattern (+ x y), but we'd like (+ z z)
(define (check/reduce-redundant-pair abstraction var1 var2)
  (let* ([vars (abstraction->vars abstraction)]
         [ahist (abstraction-instances->get-instances abstraction)]
         [var1-history (abstraction-history->var-history ahist var1)]
         [var2-history (abstraction-history->var-history ahist var2)])
    (if (equal? var1-history var2-history)
        (abstraction->combine-variables abstraction var1 var2)
        #f)))

;; remove variable2 and replace all instances in the pattern with variable1
(define (abstraction->combine-variables abstraction var1 var2)
  (let* ([old-pattern (abstraction->pattern abstraction)]
         [new-pattern (sexp-replace var2 var1 old-pattern)]
         [old-variables (abstraction->vars abstraction)]
         [new-variables (delete var2 old-variables)]
         [old-name (abstraction->name abstraction)])
    (make-named-abstraction old-name new-pattern new-variables)))

(define (remove-redundant-variables abstraction)
  (let ([vars (abstraction->vars abstraction)])
    (if (or (not (applied? abstraction)) (null? vars))
        abstraction
        (let* ([var-pairs (unique-commutative-pairs vars list)])
          (define (same-abstraction-recursion var-pairs)
            (if (null? var-pairs)
                abstraction
                (let* ([var-pair (first var-pairs)]
                       [pair-reduced (check/reduce-redundant-pair abstraction (first var-pair) (second var-pair))])
                  (if pair-reduced
                      (remove-redundant-variables pair-reduced)
                      (same-abstraction-recursion (rest var-pairs))))))
          (same-abstraction-recursion var-pairs)))))

(define (applied? abstraction)
  (hash-table-ref abstraction-instances
                  (abstraction->name abstraction)
                  (lambda () #f)))


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

;; replcae a few uninteresting abstractions with #f
;; (single variable or singleton list)
;; returns an abstraction or #f
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
  (define (fau st1 st2)
    (list st1 st2 (filtered-anti-unify st1 st2 ignore-id-matches)))
  (let ([sts1 (all-subtrees et1)]
        [sts2 (all-subtrees et2)])
    (apply append
           (map (lambda (st1) (map (lambda (st2) (fau st1 st2)) sts2)) sts1))))

;; return abstractions for all subtrees that enumerated tree et has in
;; common with itself, ignore identity matches
(define (self-matches et)
  (define (fau st1 st2)
    (let* ([abstraction (filtered-anti-unify st1 st2 #t)]
           [exp1 (unenumerate-tree st1)]
           [exp2 (unenumerate-tree st2)])
      (if abstraction
          (begin 
            (replace-matches exp1 abstraction)
            (replace-matches exp2 abstraction)
            (list st1 st2 (remove-redundant-variables abstraction)))
          (list st1 st2 #f))))
  (let ([sts (all-subtrees et)])
    (unique-commutative-pairs sts fau)))


;; takes a sexpr (s), a sexpr with variables (sv) and a proc name, e.g.
;; s = (foo (foo a b c) b c)
;; sv = (foo V b c)
;; name = P
;; first pass: (P (foo a b c))
;; second (operand) pass: (P (P a))
;; returns #f if abstraction cannot be applied, otherwise variable assignments
;; ! assumes that each variable occurs only once in sv [2]
(define unify
  (mem (lambda (s sv vars)
         (begin
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
                        (check/remove-repeated (apply append assignments))))])))))

;;returns false if any repeated variable in pattern doesn't have the same value or any of the assignments are false, returns a set of unique variable assignments
(define (check/remove-repeated unified-vars)
  (let* ([repeated-vars (filter more-than-one (map (curry all-assoc unified-vars) (map first unified-vars)))])
    (if (and (all (map all-equal? repeated-vars)) (not (any false? unified-vars)))
        (delete-duplicates unified-vars)
        #f)))
        

;; doesn't deal with partial matches, could use more error checking; 
(define (replace-matches s abstraction)
  (let ([unified-vars (unify s
                             (abstraction->pattern abstraction)
                             (abstraction->vars abstraction))])
    (if (false? unified-vars)
        (if (list? s)
            (map (lambda (si) (replace-matches si abstraction)) s)
            s)
        (begin
          (abstraction-instances->add-instance! abstraction unified-vars)
          (pair (abstraction->name abstraction)
                (map (lambda (var) (replace-matches (rest (assq var unified-vars)) abstraction))
                     (abstraction->vars abstraction)))))))


;; throw out any matches that are #f
(define (get-valid-abstractions subtree-matches)
  (let ([abstractions (map third subtree-matches)])
    (filter (lambda (x) x) abstractions)))

(define (get/make-valid-abstractions subtree-matches)
  (let* ([abstractions (map third subtree-matches)]
         [non-false (filter (lambda (x) x) abstractions)]
         [no-free-vars (map capture-vars non-false)])
    no-free-vars))

(define (capture-vars abstraction)
  (let* ([free-vars (get-free-vars abstraction)]
         [new-vars (append free-vars (abstraction->vars abstraction))]
         [old-pattern (abstraction->pattern abstraction)]
         [old-name (abstraction->name abstraction)])
    (if (null? free-vars)
        abstraction
        (let ([no-free-abstraction (make-named-abstraction old-name old-pattern new-vars)])
          (hash-table-update! abstraction-instances old-name (lambda (original) (make-abstraction-history new-vars)))
          no-free-abstraction)
          )))

(define (get-free-vars abstraction)
  (let* ([pattern (abstraction->pattern abstraction)]
         [non-free (abstraction->vars abstraction)]
         [free '()]
         [free-var? (lambda (x) (and (var? x) (not (member x non-free))))]
         [add-to-free! (lambda (x) (set! free (pair x free)))])
    (sexp-search free-var? add-to-free! pattern)
    free))

        

  

;; joins definitions and program body into one big list
(define (condense-program program)
  `(,@(map abstraction->pattern (program->abstractions program))
    ,(program->body program)))

;; compute a list of compressed programs
(define (compressions program)
  (let* ([condensed-program (condense-program program)]
         [abstractions (self-matches (enumerate-tree condensed-program))]
         [valid-abstractions (get/make-valid-abstractions abstractions)] ;; [1]
         [compressed-programs (map (curry compress-program program) valid-abstractions)]
         [program-size (size (program->sexpr program))]
         [valid-compressed-programs (filter (lambda (cp) (<= (size (program->sexpr cp))
                                                             (+ program-size 1)))
                                            compressed-programs)])
    valid-compressed-programs))

;; both compressee and compressor are abstractions
(define (compress-abstraction compressor compressee)
  (make-named-abstraction (abstraction->name compressee)
                          (replace-matches (abstraction->pattern compressee) compressor)
                          (abstraction->vars compressee)))

(define (compress-program program abstraction)
  (let* ([compressed-abstractions (map (curry compress-abstraction abstraction)
                                       (program->abstractions program))]
         [compressed-body (replace-matches (program->body program) abstraction)])
    (make-program (pair abstraction compressed-abstractions)
                  compressed-body)))

;; iteratively compress program, filter programs using cfilter before recursing
(define (iterated-compressions cfilter program)
  (let ([compressed-programs (cfilter (compressions program))])
    (append compressed-programs
            (apply append (map (curry iterated-compressions cfilter) compressed-programs)))))

;; compute all entries of full (semi)lattice
(define all-iterated-compressions
  (curry iterated-compressions (lambda (x) x)))

;; before exploring, boil down set of programs to eliminate duplicates
;; NOTE: uses unique-programs which currently compares by length!
(define unique-iterated-compressions
  (curry iterated-compressions unique-programs))

;; NOTE: uses unique-programs which currently compares by length!
(define (beam-search-compressions n program)
  (iterated-compressions (lambda (progs) (shortest-n n (unique-programs progs)))
                         program))


;; testing

(define (pretty-print-match m)
  (for-each display
            (list "t1: " (unenumerate-tree (first m)) "\n"
                  "t2: " (unenumerate-tree (second m)) "\n"
                  "m: " (abstraction->pattern (third m)) "\n\n")))

(define (pretty-print-program program)
  (let ([sexpr (program->sexpr program)])
    (pretty-print sexpr)
    (for-each display (list "size: " (size sexpr) "\n\n"))))

(define (test-unify)
  (let* ([sexpr '(a b c d)]
         [pattern '(A b c A)] 
         [variables '(A B)]) 
    (pretty-print (unify sexpr pattern variables))))
;;((A . a)) correct output?!
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
  (let* ([test-tree '(e f ((d (a b c)) b c) g h (e f (q q)))]
         [abstraction (make-abstraction '(X b Y) '(X Y))]
         [abstraction2 (make-abstraction '(e f Z) '(Z))])
    (pretty-print (replace-matches test-tree abstraction))
    (pretty-print (replace-matches test-tree abstraction2))))

(define (test-compression sexpr)
  (for-each display (list "original expr:\n" sexpr "\n"
                          "size: " (size sexpr)
                          "\n\n"
                          "compressed exprs:\n"))
  (map pretty-print-program
       (sort-by-size
        (unique-programs
         (beam-search-compressions 100 (make-program '() sexpr))))))

(define (test-redundant-variables)
  (let* ([tabs (make-abstraction '(+ A B C D) '(A B C D))]
         [test-trees '((+ a b b a) (+ q d d q) (+ f m m f))])
;         [test-trees '((+ 2 3 3 2) (+ 4 5 5 4) (+ 6 1 1 6))])
    (map (lambda (x) (replace-matches x tabs)) test-trees)
    (pretty-print test-trees)    
    (pretty-print tabs)
    (pretty-print (remove-redundant-variables tabs))))


;the expression should have a pattern with repeated variables
(define (test-repeated-variable-pattern)
  (let* ([expr '(+ (+ a b a) (+ c d c))]
         [et (enumerate-tree expr)])
    (pretty-print (self-matches et))))

(define (test-capture-vars)
  (pretty-print (capture-vars (make-abstraction '(v1 v2 (f a v3)) '(v3)))))

;;(test-capture-vars)

;(test-repeated-variable-pattern)
(test-compression '(h (m (h (m (h (m (h (m (c))))))))))
;(test-compression '(f (a x) (f (a x) (f (a x) b (a x)) (a x)) (a x)))
;; (test-compression '(f (a b (x y (u k l)))
;;                       (a b c)
;;                       (a b (z d (u k l)))
;;                       (a b c)))
;; (test-compression '(a (a (foo bar) b) (a (bar foo) b) (a (bzar fzoo) b)))
;;(test-compression '(f (a x) (f (a x) (f (a x) b (a x)) (a x)) (a x)))
 ;; (test-compression '(k (h (g (f (a b (x y (u k l)))
 ;;                               (a b c)
 ;;                               (a b (z d (u k l)))
 ;;                               (a b c))
 ;;                            (f (a b (x y (u k l)))
 ;;                               (a b c)
 ;;                               (a b (z d (u k l)))
 ;;                               (a b c)))
 ;;                         (g (f (a b (x y (u k l)))
 ;;                               (a b c)
 ;;                               (a b (z d (u k l)))
 ;;                               (a b c))
 ;;                            (f (a b (x y (u k l)))
 ;;                               (a b c)
 ;;                               (a b (z d (u k l)))
 ;;                               (a b c))))
 ;;                      (h (g (f (a b (x y (u k l)))
 ;;                               (a b c)
 ;;                               (a b (z d (u k l)))
 ;;                               (a b c))
 ;;                            (f (a b (x y (u k l)))
 ;;                               (a b c)
 ;;                               (a b (z d (u k l)))
 ;;                               (a b c)))
 ;;                         (g (f (a b (x y (u k l)))
 ;;                               (a b c)
 ;;                               (a b (z d (u k l)))
 ;;                               (a b c))
 ;;                            (f (a b (x y (u k l)))
 ;;                               (a b c)
 ;;                               (a b (z d (u k l)))
 ;;                               (a b c))))))

;(test-compression '((f (f (f (f x)))) (g (g (g (g x))))))


;;
;;write get-free-vars
;;write var?