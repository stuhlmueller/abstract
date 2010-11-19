#!r6rs

(library (util)
         (export all-equal? all-assoc curry all max-take sexp-replace sexp-search get/make-alist-entry)
         (import (except (rnrs) string-hash string-ci-hash)
                 (only (ikarus) set-car! set-cdr!)
                 (_srfi :1)
                 (_srfi :69)
                 (church readable-scheme))

         (define (all-equal? lst)
           (all (map (lambda (itm) (equal? (first lst) itm)) (rest lst))))

         (define (all-assoc alist key)
           (filter (lambda (entry) (equal? (first entry) key)) alist))

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
         ;;if abstract.ss stops working replace sexp-replace in abstract.ss w/ a function leaf replace (sexp-replace before it was modified to the current version)
         (define (sexp-replace old new sexp)
           (if (equal? old sexp)
               new
               (if (list? sexp)
                   (map (curry sexp-replace old new) sexp)
                   sexp)))
               

         (define (sexp-search pred? func sexp)
           (if (list? sexp)
               (map (curry sexp-search pred? func) sexp)
               (if (pred? sexp) (func sexp) sexp)))

                  ;; look up value for key in alist; if not found,
         ;; set (default-thunk) as value and return it
         (define (get/make-alist-entry alist alist-set! key default-thunk)
           (let ([binding (assq key alist)])
             (if binding
                 (rest binding)
                 (let* ([default-val (default-thunk)])
                   (alist-set! key default-val)
                   default-val))))
)
