#lang racket/unit

(require "../utils/utils.rkt" 
         "signatures.rkt"
         racket/match
         syntax/parse
         (env lexical-env)
         (private syntax-properties)
         (rep type-rep)
         (typecheck check-below)
         (types abbrev tc-result)
         (utils tc-utils))

(import tc-expr^)
(export tc-for^)

(define (tc/for stx expected)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [(let-values ()
       (#%expression
        (#%plain-lambda ()
          (let-values ([_ rhs] ...)
            (#%plain-app _))))
       for-loop)
     (define *bodies (find-loop-bodies #'for-loop))
     (match-define (cons names-stx bodies) *bodies)
     (define rhs-stxs (syntax->list #'(rhs ...)))
     (define clause-names (parse-clause-names names-stx))
     (define-values (*names *types)
       (for/lists (_1 _2)
                  ([names-stx (in-list clause-names)]
                   [rhs-stx (in-list rhs-stxs)])
         (define names (syntax->list names-stx))
         (define result (tc-expr rhs-stx))
         ;; if there are the wrong number of values, report it now
         (check-below
          result
          (apply ret (build-list (length names) (λ (_) Univ))))
         ;; at this point we can assume we have the right # of values
         (define elem-types
           (map seq->elem-type (match result [(tc-results: ts) ts])))
         (values names elem-types)))
     (define-values (names types)
       (values (apply append *names) (apply append *types)))
     (printf "names ~a types ~a~n" names types)
     (define bodies-result
       (with-lexical-env/extend-types names types
         ;; FIXME expected
         (tc-body/check #`#,bodies #f)))
     (match bodies-result
       ;; FIXME other cases
       [(tc-result1: t f o)
        (ret (-lst t) f o)])]))

;; Type -> Type
(define (seq->elem-type type)
  (displayln type)
  (match type
    [(Sequence: (list t)) t]
    ;; FIXME
    [_ (int-err "foo")]))

;; Invariant: the first loop body found is always a special one
;;            that stores names that TR will track.
(define (find-loop-bodies stx)
  (reverse
   (let loop ([form stx] [bodies null])
     (syntax-parse form
       #:literal-sets (kernel-literals)
       [stx:tr:for:body^
        (cons form bodies)]
       [(e ...)
        (for/fold ([bodies bodies])
                  ([e (in-list (syntax->list #'(e ...)))])
          (loop e bodies))]
       [x bodies]))))

;; Syntax -> (Listof Syntax)
(define (parse-clause-names stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [(#%expression
      (#%plain-lambda ()
        (let-values ([_ (#%plain-app _ . clause-names)] ...)
          _)))
     (displayln (syntax->list #'(clause-names ...)))
     (syntax->list #'(clause-names ...))]
    [_ (displayln "boom") (displayln (syntax->datum stx))]))
