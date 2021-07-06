#lang racket
(provide (all-defined-out))

(require "ast.rkt")

;; Expr -> Boolean
;; Is x a well-formed expression?
(define (expr? x)
  (match x
    [(int-e i)    #t]
    [(bool-e b)   #t]
    [(var-e v)    #t]
    [(char-e c)   #t]
    [(string-e s) #t]
    [(nil-e)      #t]
    [(if-e p t f)
     (and (expr? p)
          (expr? t)
          (expr? f))]
    [(prim-e p es) (and
                    (prim? p)
                    (andmap expr? es))]
    [(cond-e cs f)
       (and (andmap expr? (get-preds cs))
            (andmap expr? (get-bods cs))
            (expr? f))]
    [(let-e bs b)
     (and (bindings? bs)
          (not (check-duplicates (get-vars bs) eq?))
          (expr? b))]
    [_ #f]))

;; Expr -> Boolean
;; Is e a closed expression?
(define (closed? e)
  (closed?helper e '()))

(define (has-var c v)
  (match c
    ['() #f]
    [(cons (var-e f) t) (if  (eq? f v) #t (has-var t v))]
    ))

;; Any -> Boolean
;; Is x a well-formed list of bindings?
(define (bindings? xs)
  (match xs
    ['() #t]
    [(cons (binding v e) bs) (and
                               (symbol? v)
                               (bindings? bs))]))

;; Any -> Boolean
(define (keyword? x)
  (and (symbol? x)
       (memq x '(cond else if))))

; SExpr -> AST
; Parse the s-expr into our AST
; This should be a one-to-one mapping for now.
(define (sexpr->ast s)
  (match s
    [(? symbol? v)  (var-e v)]
    [(? integer? i) (int-e i)]
    [(? char? c)    (char-e c)]
    [(? string? s)  (string-e s)]
    [(? boolean? b) (bool-e b)]
    [''()           (nil-e)]
    [`(,(? prim1? p) ,e)
         (prim-e p (list (sexpr->ast e)))]
    [`(,(? prim2? p) ,e1 ,e2)
         (prim-e p (list (sexpr->ast e1) (sexpr->ast e2)))]
    [`(if ,p ,t ,f) (if-e (sexpr->ast p) (sexpr->ast t) (sexpr->ast f))]
    [`(cond ,@cs)
      ; collect the clauses in a pair where the car
      ; is the list of clauses the cdr is the 'else'
      (let ((p (clauses->ast '() cs))) 
        (cond-e (car p) (cdr p)))]
    [`(let ,bs ,b)          (let-e (map binding->ast bs) (sexpr->ast b))]
    [o              (error "operation not supported: " o)]))

(define (clauses->ast acc cs)
  (match cs
    [`((else ,f))
      (cons (reverse acc) (sexpr->ast f))]
    [(cons `(,e ,b) rest)
      (let ((c (clause (sexpr->ast e) (sexpr->ast b))))
           (clauses->ast (cons c acc) rest))]))

(define (binding->ast bs)
  (match bs
    [`(,(? symbol? v) ,e) (binding v (sexpr->ast e))]
    [_                    (error "bound name must be a symbol")]))


(define (closed?helper e c)
  (match e
    [(int-e i)     #t]
    [(bool-e b)    #t]
    [(char-e c)    #t]
    [(string-e s)  #t]
    [(var-e v)     (and (memq v c) #t)]
    [(nil-e)       #t]
    [(if-e p t f)  (and
                     (closed?helper p c)
                     (closed?helper t c)
                     (closed?helper f c))]
    [(prim-e (? prim1? p) (list e))
      (closed?helper e c)]
    [(prim-e (? prim2? p) (list e0 e1))
      (and (closed?helper e0 c)
           (closed?helper e1 c))]
    [(cond-e cs f) (and
                     (closed-clauses? cs c)
                     (closed?helper f c))]
    [(let-e bs e)  (let ((vs (get-vars bs)))
                        (and
                          (closed-bindings? bs c)
                          (closed?helper e (append vs c))))]))

(define (closed-clauses? cs c)
  (match cs
    ['() #t]
    [(cons (clause e b) cs) (and
                              (closed?helper e c)
                              (closed?helper b c)
                              (closed-clauses? cs c))]))

(define (closed-bindings? bs c)
  (match bs
    ['() #t]
    [(cons (binding v def) bs) (and
                                 (closed?helper def c)
                                 (closed-bindings? bs c))]))
