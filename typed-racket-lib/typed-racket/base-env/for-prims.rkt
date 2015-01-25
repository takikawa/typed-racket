#lang racket/base

(require "../utils/utils.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     (base-env annotate-classes)
                     (private syntax-properties)))

(provide for/list:
         for/and:
         for/or:
         for/first:
         for/last:
         for/hash:
         for/sum:
         for/product:
         for/hasheq:
         for/hasheqv:
         for/fold:)

;; FIXME
(define-for-syntax (add-ann expr-stx ty-stx)
  (quasisyntax/loc expr-stx
    (#,(type-ascription-property #'#%expression ty-stx)
     #,expr-stx)))

(begin-for-syntax
  (define-syntax-class accum-clause
    #:attributes (name rhs new-form)
    (pattern [n:optionally-annotated-name rhs:expr]
             #:with name #'n.ann-name
             #:with new-form #'[n.ann-name rhs]))

  (define-splicing-syntax-class for-clause
    #:attributes (names names-val rhs new-form)
    (pattern [n:optionally-annotated-name rhs:expr]
             #:with names #'(n.ann-name)
             #:with names-val #'(values n.ann-name)
             #:with new-form #'([n.ann-name rhs]))
    (pattern [(n:optionally-annotated-formal ...) rhs:expr]
             #:with names #'(n.ann-name ...)
             #:with names-val #'(values n.ann-name ...)
             #:with new-form #'([(n.ann-name ...) rhs]))
    (pattern (~seq (~and kw (~or #:when #:unless
                                 #:break #:final))
                   seq-rhs)
             #:attr rhs #f
             #:attr names #f
             #:attr names-val #f
             #:attr ann-rhs (tr:for:when-property #'seq-rhs (syntax-e #'kw))
             #:with new-form #`(kw #,(attribute ann-rhs))))

  (define-splicing-syntax-class optional-standalone-annotation*
    #:attributes (ty annotate)
    (pattern :optional-standalone-annotation
      #:attr annotate (λ (stx) (if (attribute ty)
                                   (add-ann stx #'ty)
                                   stx)))))

(define-syntax (define-for-variants stx)
  (syntax-parse stx
    [(_ (name untyped-name (~optional (~and (~seq #:accum)
                                            (~bind [accum? #'#t]))
                                      #:defaults ([accum? #'#f])))
        ...)
     (quasisyntax/loc stx
       (begin (define-syntax name (define-for-variant #'untyped-name accum?))
              ...))]))

(define-for-syntax ((define-for-variant untyped-name accum?) stx)
  (syntax-parse stx
    [(_
      a1:optional-standalone-annotation*
      ;; a pattern for expressing ~if
      (~or (~and (~parse #t accum?)
                 (accum:accum-clause ...))
           (~and (~parse #f accum?)
                 (~and (~seq) (~bind [(accum.name 1) null]
                                     [(accum.rhs 1) null]
                                     [(accum.new-form 1) null]))))
      (clause:for-clause ...)
      a2:optional-standalone-annotation*
      body ...) ; body is not always an expression, can be a break-clause
     (define body-forms (syntax->list #'(body ...)))
     (define/with-syntax (rhs ...) (filter values (attribute clause.rhs)))
     (define/with-syntax (names ...) (filter values (attribute clause.names)))
     (define/with-syntax (names-val ...) (filter values (attribute clause.names-val)))
     (define new-forms (apply append (map syntax->list (syntax->list #'(clause.new-form ...)))))
     ((attribute a1.annotate)
      ((attribute a2.annotate)
       (tr:for
        (quasisyntax/loc stx
          (let-values ()
            (quote #,(syntax-e untyped-name))
            (quote #,accum?)
            (λ ()
              ;; for potential accumulator bindings
              (let-values ([(accum.name) accum.rhs] ...)
                (void))
              ;; for the loop bindings
              (let-values ([names rhs] ...)
                (void)))
            (#,untyped-name #,@(if accum?
                                   #'((accum.new-form ...))
                                   #'())
                            (#,@new-forms)
              #,(tr:for:body
                 #'(λ ()
                     ;; same order as above
                     (let-values ([(accum.name) accum.name] ...)
                       (void))
                     (let-values ([names names-val] ...)
                       (void))))
              #,@(map tr:for:body body-forms)))))))]))

(define-for-variants
  (for/list: for/list)
  (for/and: for/and)
  (for/or: for/or)
  (for/first: for/first)
  (for/last: for/last)
  (for/sum: for/sum)
  (for/product: for/product)
  (for/hash: for/hash)
  (for/hasheq: for/hasheq)
  (for/hasheqv: for/hasheqv)
  (for/fold: for/fold #:accum))
