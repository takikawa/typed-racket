#lang racket/unit

(require "../utils/utils.rkt" 
         "signatures.rkt"
         racket/function
         racket/match
         syntax/parse
         (env lexical-env)
         (private syntax-properties type-annotation)
         (rep type-rep)
         (typecheck check-below)
         (types abbrev numeric-tower subtype tc-result union)
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
         (define expected-types
           (for/list ([name names])
             (match (get-type name #:default 'no-type-found)
               ['no-type-found #f] ; for expected type
               [type type])))
         (define expected-result
           ;; FIXME: is this the best behavior? Synthesize if no annotations
           ;;        are given, assume Any for partial annotations.
           (if (andmap not expected-types)
               #f
               (ret (apply -seq (map (λ (x) (or x Univ)) expected-types)))))
         (define result (tc-expr/check/t rhs-stx expected-result))
         (define elem-types (seq->elem-type result))
         (check-seq-length result elem-types names)
         (check-binding-annotations elem-types names)
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
;; Converts a sequence type to element types, with special
;; cases for various base types
(define (seq->elem-type type)
  (match type
    [(Sequence: ts) ts]
    [(Hashtable: k v) (list k v)]
    [(Listof: t) (list t)]
    [(List: ts) (list (apply Un ts))]
    [(Set: t) (list t)]
    [(== -Bytes) (list -Byte)]
    [(? (curryr subtype -Nat)) (list type)]
    ;; FIXME
    [_ (int-err "foo")]))

;; (Listof Type) (Listof Id) -> Void
;; Invariant: check-seq-length is called first so we can
;;            assume input lists of the same length
(define (check-binding-annotations elems names)
  (for/list ([elem (in-list elems)]
             [name (in-list names)])
    (check-below elem (get-type name #:default Univ))))

;; Type (Listof Type) (Listof Id) -> Void
;; Check that the for loop binding has the right number of values
(define (check-seq-length seq-type elems names)
  (when (not (= (length elems) (length names)))
    (tc-error/fields "type mismatch in for loop clause"
                     #:more "sequence has wrong number of values"
                     "expected" (format "sequence with ~a values"
                                        (length names))
                     "given" seq-type)))

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
     (syntax->list #'(clause-names ...))]
    [_ (int-err "wrong expansion")]))
