#lang racket/base

(require "../utils/utils.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     (base-env annotate-classes)
                     (private syntax-properties)))

(provide for/list:)

;; FIXME
(define-for-syntax (add-ann expr-stx ty-stx)
  (quasisyntax/loc expr-stx
    (#,(type-ascription-property #'#%expression ty-stx)
     #,expr-stx)))

(begin-for-syntax
  (define-syntax-class for-clause
    #:attributes (names names-val rhs new-form)
    (pattern [n:optionally-annotated-name rhs:expr]
             #:with names #'(n.ann-name)
             #:with names-val #'(values n.ann-name)
             #:with new-form #'[n.ann-name rhs])
    (pattern [(n:optionally-annotated-formal ...) rhs:expr]
             #:with names #'(n.ann-name ...)
             #:with names-val #'(values n.ann-name ...)
             #:with new-form #'[(n.ann-name ...) rhs])
    ;(pattern (~seq #:with ))
    )

  (define-splicing-syntax-class optional-standalone-annotation*
    #:attributes (ty annotate)
    (pattern :optional-standalone-annotation
      #:attr annotate (λ (stx) (if (attribute ty)
                                   (add-ann stx #'ty)
                                   stx)))))

(define-syntax (for/list: stx)
  (syntax-parse stx
    [(_
      a1:optional-standalone-annotation*
      (clause:for-clause ...)
      a2:optional-standalone-annotation*
      body ...) ; body is not always an expression, can be a break-clause
     (define body-forms (syntax->list #'(body ...)))
     ((attribute a1.annotate)
      ((attribute a2.annotate)
       (tr:for
        (quasisyntax/loc stx
          (let-values ()
            (λ ()
              (let-values ([clause.names clause.rhs] ...)
                (void)))
            (for/list (clause.new-form ...)
              #,(tr:for:body
                 #'(λ ()
                     (let-values ([clause.names clause.names-val] ...)
                       (void))))
              #,@(map tr:for:body body-forms)))))))]))
