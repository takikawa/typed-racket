#lang racket/unit

(require "../utils/utils.rkt" 
         "signatures.rkt"
         racket/function
         racket/match
         syntax/parse
         syntax/parse/experimental/reflect
         (env global-env lexical-env)
         (private syntax-properties type-annotation)
         (rep filter-rep type-rep)
         (typecheck check-below tc-envops)
         (types abbrev numeric-tower subtype tc-result union)
         (utils tc-utils)
         (for-template racket/base))

(import tc-expr^ tc-apply^)
(export tc-for^)

(define (tc/for stx expected)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [(let-values ()
       (quote for-kw)
       (#%expression
        (#%plain-lambda ()
          (let-values ([_ rhs] ...)
            (#%plain-app _))))
       for-loop)
     (define kind (syntax-e #'for-kw))
     (define *bodies (find-loop-bodies #'for-loop))
     (match-define (cons names-stx bodies) *bodies)
     (define rhs-stxs (syntax->list #'(rhs ...)))
     (define clause-names (parse-clause-names names-stx))
     (define-values (names types)
       (for/fold ([names null] [types null])
                 ([names-stx (in-list clause-names)]
                  [rhs-stx (in-list rhs-stxs)])
         (define new-names (syntax->list names-stx))
         (define expected-types
           (for/list ([name new-names])
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
         (check-seq-length result elem-types new-names)
         (check-binding-annotations elem-types new-names)
         (values (append names new-names)
                 (append types elem-types))))
     (printf "names ~a types ~a~n" names types)
     ;; FIXME: this includes names that aren't bound in some #:when clauses
     (define props
       (with-lexical-env/extend-types names types
         (for/fold ([props -no-filter])
                   ([when-clause (in-list (find-whens #'for-loop))])
           (define kind (tr:for:when-property when-clause))
           (define results (tc-expr when-clause))
           (match results
             [(tc-results: _ (list (FilterSet: f+ f-) ...) _)
              (match kind
                ['#:when f+]
                ['#:unless f-]
                [_ null])]
             [_ null]))))
     (displayln props)
     (define bodies-result
       (with-lexical-env/extend-types names types
         (with-lexical-env/extend-props props
           (tc-body/check #`#,bodies (make-for-body-expected kind expected)))))
     (check-for-result kind bodies-result)]))

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

;; Symbol (U TC-Results #f) -> (U TC-Results #f)
(define (make-for-body-expected kind expected)
  (match expected
    [#f #f]
    [(tc-result1: t f o)
     (match kind
       [(or 'for/hash 'for/hasheq 'for/hasheqv)
        (match t
          [(Hashtable: k v) (ret (list k v))]
          [_ #f])]
       [(or 'for/sum 'for/product)
        (match t
          [(? (curryr subtype -Number)) (ret t)]
          [_ #f])]
       ['for/list
        (match t
          [(Listof: t) (ret t)]
          [(List: ts) (ret (apply Un ts))]
          [_ #f])]
       [(or 'for/first 'for/last 'for/and 'for/or)
        expected]
       [_ #f])]
    [(tc-results: ts fs os)
     ;; FIXME: only relevant for for/fold, for/lists, etc.
     #f]
    [(tc-any-results: _)
     #f]))

;; Symbol TC-Results -> TC-Results
(define (check-for-result kind result)
  (match result
    [(tc-result1: t f o)
     (match kind
       ['for/list (ret (-lst t))]
       [(or 'for/sum 'for/product)
        (define tmps (generate-temporaries '(1)))
        ;; FIXME: this is hackish and gives poor error messages
        ;;        and sometimes has bad type precision.
        (with-lexical-env/extend-types tmps (list (-lst t))
          (tc/apply (if (eq? kind 'for/sum) #'+ #'*)
                    #`#,tmps))]
       [(or 'for/first 'for/last 'for/and 'for/or)
        (ret t)])]
    [(tc-results: ts fs os)
     (match kind
       [(or 'for/hash 'for/hasheq 'for/hasheqv)
        #:when (= (length ts) 2)
        (ret (-HT (car ts) (cadr ts)))]
       [_ (tc-error/fields "type mismatch"
                           #:more "wrong number of values"
                           "given" (length ts))])]
    [(tc-any-results: _)
     (int-err "foo")]))

;; Invariant: the first loop body found is always a special one
;;            that stores names that TR will track.
(define (find-loop-bodies stx)
  (find-stx-class (reify-syntax-class tr:for:body^) stx))

;; Finds #:when clauses and other related clauses
(define (find-whens stx)
  (find-stx-class (reify-syntax-class tr:for:when^) stx))

(define (find-stx-class cls stx)
  (reverse
   (let loop ([form stx] [bodies null])
     (syntax-parse form
       #:literal-sets (kernel-literals)
       [(~reflect var (cls))
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
