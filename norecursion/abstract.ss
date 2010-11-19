#!r6rs

;; TODO:


;; - make a test case for getting anonymous functions when inlining
;; - inlining with higher-order functions leads to loss of irreducibility through the creation of anonymous functions? rewrite applied lambdas in the body of a program 
;; - modify abstraction-instances to have bounded size
(library (abstract)
         (export compressions abstraction-proposer sexpr->program proposal beam-compression make-program  pretty-print-program program->sexpr size get-abstractions make-abstraction abstraction->define define->abstraction)
         (import (except (rnrs) string-hash string-ci-hash)
                 (only (ikarus) set-car! set-cdr!)
                 (_srfi :1)
                 (_srfi :69)
                 (church readable-scheme)
                 (util)
                 (sym)
                 (mem))

         (define (identity x) x)

         (define (more-than-one lst)
           (> (length lst) 1))

         ;; compute the size of a program
         (define (size tree)
           (if (list? tree)
               (cond [(tagged-list? tree 'begin) (size (rest tree))] ;; ignore 'begin symbol
                     [(tagged-list? tree 'define) (size (cddr tree))] ;; ignore 'define symbol + args
                     [else (apply + (map size tree))])
               1))

         (define (unique-commutative-pairs lst func)
           (define (recursion lst1 lst2)
             (if (null? lst2)
                 '()
                 (let ((from1 (first lst1)))
                   (append (map (lambda (from2) (func from1 from2)) lst2)
                           (recursion (rest lst1) (rest lst2))))))
           (recursion lst (rest lst)))

         ;;language specific functions ;use reg-exps
         ;;temp fix b/c problems access to srfi 13
         (define (var? expr)
           (if (symbol? expr)
               (let* ([var-pattern "v"]
                      [string-expr (symbol->string expr)])
                 ;; (string-prefix? var-pattern string-expr))))
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
           `(let ()  
              ,@(map abstraction->define (program->abstractions program))
              ,(program->body program)))

         ;;assumes format of (let () definitions body); if format fails to hold then program is an empty set of abstractions and the sexpr as the body
         (define (sexpr->program sexpr)
           (define (abstraction-sexpr? x)
             (if (and (not (null? x)) (list? x))
                 (equal? (first x) 'define)
                 #f))
           (let*-values ([(no-scope-sexpr) (remove-scope sexpr)]
                         [(abstractions body) (span abstraction-sexpr? no-scope-sexpr)])
             (make-program (map define->abstraction abstractions) (first body))))

         (define (remove-scope sexpr)
           (define (scope? x)
             (or (equal? 'let x) (null? x)))
           (let*-values ([(scope program) (span scope? sexpr)])
             program))
         
         (define (get-abstractions sexpr)
           (define (abstraction-sexpr x)
             (if (and (not (null? x)) (list? x))
                 (equal? (first x) 'define)
                 #f))
           (define (get-defines sexpr)
             (if (list? sexpr)
                 (filter 
                         sexpr)
                 '()))
           (map define->abstraction (get-defines sexpr)))

         (define (define->abstraction definition)
           (let* ([name (first (second definition))]
                  [vars (rest (second definition))]
                  [body (third definition)])
             (make-named-abstraction name body vars)))

         ;;assumes program in sexpr form is (let () definitions body)
         (define (get-body sexpr)
           #f)

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
         ;; otherwise tree with variable in places where they differ
         ;; returns for (the enumerated version of) trees
         ;; (z (a (x (i (j)) (h (m)))) (c) (d (f) (i)))
         ;; (z (a (x (k (l)) (h (m)))) (c) (d (h (f)) (i)))
         ;; this:
         ;; (z (a (x (* (*)) (h (m)))) (c) (d * (i)))
         ;; (f (f (f c)))
         ;; (f (f c))
         ;; returns:
         ;; (if (flip) var2 (var1 (rec
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

         (define (base-case? pattern var)
           (equal? (second (third pattern)) var))

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

         ;;compress a single step, used as a mcmc proposal
         (define (inverse-inline program prob-of-inverse-inline)
           (pretty-print "inverse-inline")
           (let* ([possible-compressions (compressions program)])
             (if (null? possible-compressions)
                 (list program prob-of-inverse-inline prob-of-inverse-inline)
                 (let* ([compression-choice (uniform-draw possible-compressions)]
                        [fw-prob (* prob-of-inverse-inline (/ 1 (length possible-compressions)))]
                        ;;backward probability is the probability of choosing the abstraction to inline
                        [abstractions (program->abstractions compression-choice)]
                        [bw-prob (* (- 1 prob-of-inverse-inline) (/ 1 (length abstractions)))])
                   (list compression-choice fw-prob bw-prob)))))

         ;;returns a new proposal along with forward/backward probability, used in mcmc
         (define (proposal program)
           (let ([prob-of-inline .5])
             (if (flip prob-of-inline)
                 (inline program prob-of-inline)
                 (inverse-inline program (- 1 prob-of-inline)))))

         (define (abstraction-proposer sexpr)
           (define get-program first)
           (define get-fw-prob second)
           (define get-bw-prob third)
           (let* ([program (sexpr->program sexpr)]
                  [new-program+fw+bw (proposal program)]
                  [new-sexpr (program->sexpr (get-program new-program+fw+bw))]
                  [fw-prob (get-fw-prob new-program+fw+bw)]
                  [bw-prob (get-bw-prob new-program+fw+bw)])
             (list new-sexpr fw-prob bw-prob)))

         ;;inlining or decompression code; returns an expanded program and the probability of moving to that particular expansion
         (define (inline program prob-of-inline)
           (pretty-print "inline")
           (let* ([abstractions (program->abstractions program)])
             (if (null? abstractions)
                 ;;is this right? if you inline a program w/o abstraction you cannot get back by inverse-inlining (unless the inverse-inline has no possible abstractions) so should we use the prob-of-inline as the probability of returning to this state
                 (list program prob-of-inline prob-of-inline) 
                 (let* ([inline-choice (uniform-draw abstractions)]
                        [remaining-abstractions (delete inline-choice abstractions)]
                        [fw-prob (* prob-of-inline (/ 1 (length abstractions)))]
                        [inlined-program (inverse-replace-matches inline-choice (make-program remaining-abstractions (program->body program)))]
                        ;;backward probability is the probability of choosing the abstraction we inlined times probability of inverse inlining
                        [possible-compressions (compressions inlined-program)]
                        [bw-prob (* (- 1 prob-of-inline) (/ 1 (length possible-compressions)))])
                   (list inlined-program fw-prob bw-prob)))))
         

         ;;given a program body and an abstraction replace all function applications of teh abstraction in the body with the instantiated pattern
         ;;FIXME needs to be called recursively on subexpressions
         (define (inverse-replace-matches abstraction sexpr)
           (cond
            [(abstraction-instance? sexpr abstraction)
             (if (list? sexpr)
                 (instantiate-pattern (map (curry inverse-replace-matches abstraction) sexpr) abstraction)
                 (instantiate-pattern sexpr abstraction))]
            [(list? sexpr) (map (curry inverse-replace-matches abstraction) sexpr)]
            [else sexpr]))

         ;;test whether an expression is an application of the abstraction e.g. (F 3 4) for the abstraction F, also checks if abstraction is being used in higher-order function e.g. (G 3 F)
         (define (abstraction-instance? sexpr abstraction)
           (if (and (list? sexpr) (not (null? sexpr)))
               (let* ([name (abstraction->name abstraction)]
                      [num-vars (length (abstraction->vars abstraction))]
                      [num-vals (length (rest sexpr))])
                 (and (equal? (first sexpr) name) (eq? num-vars num-vals)))
               (if (equal? (abstraction->name abstraction) sexpr) #t #f)))


         ;;the sexpr is of the form (F arg1...argN) where F is the name of the abstraction and N is the number of variables in the abstraction pattern; return the pattern with all the variables replaced by the arguments to F; the first case deals with the abstraction being used in a higher-order functions; the second case deals with abstraction
         (define (instantiate-pattern sexpr abstraction)
           (cond [(equal? sexpr (abstraction->name abstraction))
                  (make-anon abstraction)]
                 [else (let* ([var-values (rest sexpr)]
                              [var-names (abstraction->vars abstraction)])
                         (fold replace-var (abstraction->pattern abstraction) (zip var-names var-values)))]))

         (define (make-anon abstraction)
           `(lambda ,(abstraction->vars abstraction) ,(abstraction->pattern abstraction)))

         ;;replace the named variable in the pattern with a value
         (define (replace-var name-value pattern)
           (define name first)
           (define value second)
           (sexp-replace (name name-value) (value name-value) pattern))

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


         (define (beam-compression sexpr beam-size)
           (for-each display (list "original expr:\n" sexpr "\n"
                                   "size: " (size sexpr)
                                   "\n\n"
                                   "compressing...\n"))
           (first (sort-by-size
            (unique-programs
             (beam-search-compressions beam-size (make-program '() sexpr))))))
         
         )
    
;; - write get-body
;; - write sexpr->program so proposal can be used in bher

;; - think about whether you need to modify the abstraction-instances when inlining

;; -potential issue if you try to inline a function that calls itself and it is not in the form (f (f (f (x))))); if you start from programs without abstraction this may never occur since any recursive function should abstract to (f(f(f(x)))) form 

