#lang racket
(provide (all-defined-out))

(require "ast.rkt")

;; This assignment should be completed individually.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; I pledge on my honor that I have not given or received any
;; unauthorized assistance on this assignment.
;;
;; Name: Tsewang Thilly
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; An immediate is anything ending in #b0000
;; All other tags in mask #b111 are pointers

(define result-shift     3)
(define result-type-mask (sub1 (arithmetic-shift 1 result-shift)))
(define type-imm         #b000)
(define type-box         #b001)
(define type-pair        #b010)
(define type-string      #b011)

(define imm-shift        (+ 2 result-shift))
(define imm-type-mask    (sub1 (arithmetic-shift 1 imm-shift)))
(define imm-type-int     (arithmetic-shift #b00 result-shift))
(define imm-type-bool    (arithmetic-shift #b01 result-shift))
(define imm-type-char    (arithmetic-shift #b10 result-shift))
(define imm-type-empty   (arithmetic-shift #b11 result-shift))

(define imm-val-false    imm-type-bool)
(define imm-val-true     (bitwise-ior (arithmetic-shift 1 (add1 imm-shift)) imm-type-bool))

;; Allocate in 64-bit (8-byte) increments, so pointers
;; end in #b000 and we tag with #b001 for boxes, etc.

;; type CEnv = (Listof (Maybe Variable))
;; type Imm = Integer | Boolean | Char | '()

;; Expr -> Asm
(define (compile e)
  `(entry
    ,@(compile-e e '())
    ret
    err
    (push rbp)
    (call error)
    ret))

;; Expr CEnv -> Asm
(define (compile-e e c)
  (match e
    [(? imm? i)            (compile-imm (get-val i))]
    [(var-e v)             (compile-var v c)]
    [(prim-e p es)         (compile-prim p es c)]
    [(if-e e0 e1 e2)       (compile-if e0 e1 e2 c)]

    ;;
    
    [(cond-e cs f) (match cs
                     ['() (let ((c0 (compile-e f c))) `(,@c0))]
                     [(cons (clause condi exp) t2) (compile-e (if-e condi exp (cond-e t2 f)) c) ]
                   )]

    [(let-e cs bod) (compile-let-e cs bod c)]
    [(string-e e0) (compile-string-e e0)]
    [_ `((jmp err)) ]
    ))

;; String -> Asm
(define (compile-string-e s)
  (let ((c (compile-string-e-chars (string->list s) 1)))
    `(,@c
      (mov rax ,(imm->bits (string-length s)))
      (mov (offset rdi 0) rax)
      (mov rax rdi)
      (add rax ,type-string)
      (add rdi ,(* 8 (add1 (string-length s)))))))

;; (Listof Char) Natural -> Asm
(define (compile-string-e-chars cs i)
  (match cs
    ['() '()]
    [(cons c cs)
     `((mov rax ,(imm->bits c))
       (mov (offset rdi ,i) rax)
       ,@(compile-string-e-chars cs (add1 i)))]))

;; (Listof (List Variable Expr)) Expr CEnv -> Asm
(define (compile-let-e cs e1 c)
  (let ((c0 (compile-let-e-rhs (get-defs cs) c))
        (c1 (compile-e e1 (append (reverse (get-vars cs)) c))))
    `(,@c0
      ,@c1)))

;; (Listof Expr) CEnv -> Asm
;; Compile the RHSs of a let
(define (compile-let-e-rhs  es c)
  (match es
    ['() '()]
    [(cons e es)
     (let ((c0 (compile-e e c)))
       `(,@c0
         (mov (offset rsp ,(- (add1 (length c)))) rax)
         ,@(compile-let-e-rhs es (cons (gensym) c))))]))

(define (get-symbols s)
  (match s
    ['() '()]
    [(var-e e) e]
    [(cons (var-e e) (var-e f)) (cons e (cons f '()))]
    [(cons (var-e e)'()) e]
    [(cons (var-e e) t) (cons e (get-symbols t))]
    ))

;; Any -> Boolean
(define (imm? x)
  (or (int-e? x)
      (bool-e? x)
      (char-e? x)
      (nil-e? x)))

(define (compile-prim p es c)
  (match (cons p es)
    [`(box ,e0)            (compile-box e0 c)]
    [`(unbox ,e0)          (compile-unbox e0 c)]
    [`(cons ,e0 ,e1)       (compile-cons e0 e1 c)]
    [`(car ,e0)            (compile-car e0 c)]
    [`(cdr ,e0)            (compile-cdr e0 c)]
    [`(add1 ,e0)           (compile-add1 e0 c)]
    [`(sub1 ,e0)           (compile-sub1 e0 c)]
    [`(zero? ,e0)          (compile-zero? e0 c)]
    [`(+ ,e0 ,e1)          (compile-+ e0 e1 c)]

    ;; Many primitive are still left:
    ;; -, char=?, boolean=?, =, <, <=, string-length, string-ref,
    ;; make-string, char-integer, integer->char, abs
    ;; TODO
   [`(box? ,e0) (compile-box? e0 c)]
   [`(empty? ,e0) (compile-empty? e0 c)]
   [`(cons? ,e0) (compile-cons? e0 c)]
   [`(= ,e0 ,e1)          (compile-= e0 e1 c)]
   [`(< ,e0 ,e1)          (compile-< e0 e1 c)]
   [`(<= ,e0 ,e1)          (compile-<= e0 e1 c)]
   [`(char=? ,e0 ,e1)          (compile-char=? e0 e1 c)]
   [`(boolean=? ,e0 ,e1)          (compile-boolean=? e0 e1 c)]
   [`(string? ,e0) (compile-string? e0 c)]
   [`(string-ref ,e0 ,e1) (compile-string-e-ref e0 e1 c)]
   [`(string-length ,e0) (compile-string-e-length e0 c)]
   [`(make-string ,e0 ,e1) (compile-make-string-e e0 e1 c)]
   [`(char->integer ,e0) (compile-char->int e0 c)]
   [`(integer->char ,e0) (compile-int->char e0 c)]
   [`(abs ,e0) (compile-abs e0 c)]
   [`(- ,e0 ,e1) (compile--- e0 e1 c)]
   [`(- ,e0) (compile-- e0 c)]
   [`(char? ,e0) (compile-char? e0 c)]
   [`(integer? ,e0) (compile-integer? e0 c)]
   [`(boolean? ,e0) (compile-boolean? e0 c)]
   [_ `((jmp err))]
   ))

(define (compile-boolean? e0 c)
  (let ((c0 (compile-e e0 c))
        (l0 (gensym)))
    `(,@c0
      (mov rbx ,imm-val-true)
      (and rax #b11111)
      (cmp rax ,imm-type-bool)
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx))
    )
  )

(define (compile-integer? e0 c)
  (let ((c0 (compile-e e0 c))
        (l0 (gensym)))
    `(,@c0
      (mov rbx ,imm-val-true)
      (and rax #b11111)
      (cmp rax ,imm-type-int)
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx))
    )
  )

(define (compile-char? e0 c)
  (let ((c0 (compile-e e0 c))
        (l0 (gensym)))
    `(,@c0
      (mov rbx ,imm-val-true)
      (and rax #b11111)
      (cmp rax ,imm-type-char)
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx))
    )
  )

(define (compile-char->int e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      ,@assert-char
      (xor rax ,imm-type-char))))

(define (compile-int->char e0 c)
  (let ((c0 (compile-e e0 c)))
   `(,@c0
    (mov rbx rax)
    (and rbx ,imm-type-mask)
    (cmp rbx 0)
    (jne err)
    (cmp rax ,(arithmetic-shift -1 imm-shift))
    (jle err)
    (cmp rax ,(arithmetic-shift #x10FFFF imm-shift))
    (mov rbx rax)
    (sar rbx ,(+ 11 imm-shift))
    (cmp rbx #b11011)
    (je err)
    (xor rax ,imm-type-char))))
     

;; Expr CEnv -> Asm
(define (compile-abs e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      ,@assert-integer
      (mov rbx rax)
      (neg rax)
      (cmovl rax rbx))))

;; Expr CEnv -> Asm
(define (compile-- e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      ,@assert-integer
      (neg rax))))

;; Expr Expr CEnv -> Asm
(define (compile--- e0 e1 c)
  (let ((c1 (compile-e e1 c))
        (c0 (compile-e e0 (cons #f c))))
    `(,@c1
      ,@assert-integer
      (mov (offset rsp ,(- (add1 (length c)))) rax)
      ,@c0
      ,@assert-integer
      (sub rax (offset rsp ,(- (add1 (length c))))))))

;; Expr Expr CEnv -> Asm
(define (compile-make-string-e e0 e1 c)
  (let ((c0 (compile-e e0 c))
        (c1 (compile-e e1 (cons #f c)))
        (done (gensym 'make_string_done))
        (loop (gensym 'make_string_loop))
        (i (- (add1 (length c)))))
    `(,@c0
       ,@assert-integer
       (cmp rax -1)
       (jle err)
      (mov (offset rsp ,i) rax)
      ,@c1
       ,@assert-char
      (mov rbx (offset rsp ,i))
      (mov (offset rdi 0) rbx)
      (mov rcx rdi)
      (sar rbx ,(- imm-shift 3)) ; rbx = len*8
      (add rdi 8)
      (add rbx rdi)
      ,loop
      (cmp rbx rdi)
      (je ,done)
      (mov (offset rdi 0) rax)
      (add rdi 8)
      (jmp ,loop)
      ,done
      (mov rax rcx)
      (or rax ,type-string))))


;; Expr CEnv -> Asm
(define (compile-string-e-length e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      ,@assert-string
      (xor rax ,type-string)
      (mov rax (offset rax 0))))) 

;; Expr Expr CEnv -> Asm
(define (compile-string-e-ref e0 e1 c)
  (let ((c0 (compile-e e0 c))
        (c1 (compile-e e1 (cons #f c)))
        (i (- (add1 (length c)))))
    `(,@c0
      ,@assert-string
      (xor rax ,type-string)
      (mov (offset rsp ,i) rax)
      ,@c1
      ,@assert-integer
      ,@(assert-valid-index i)
      (sar rax 2) ;; hold i * 8
      (add rax 8) ;; skip past length
      (add rax (offset rsp ,(- (add1 (length c)))))
      (mov rax (offset rax 0)))))

;; Asm
(define (assert-valid-index i)
  `((cmp rax ,(arithmetic-shift -1 imm-shift))
    (jle err)
    (mov rbx (offset rsp ,i))
    (mov rbx (offset rbx 0))
    (cmp rbx rax)
    (jle err)))

(define (compile-string? e0 c)
  (let ((c0 (compile-e e0 c))
        (l0 (gensym)))
    `(,@c0
      (mov rbx ,imm-val-true)
      (and rax #b111)
      (cmp rax ,type-string)
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx))
    )
  )

(define (compile-char=? e0 e1 c)
  (let ((c1 (compile-e e1 c))
        (c0 (compile-e e0 (cons #f c)))
        (l0 (gensym)))
    ;; FIXME this should really do the type check *after* both
    ;; expression have executed
    `(,@c1
      ,@assert-char
      (mov (offset rsp ,(- (add1 (length c)))) rax)
      ,@c0
      ,@assert-char
      (mov rbx ,imm-val-true)
      (cmp rax (offset rsp ,(- (add1 (length c)))))
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx)
      )))

(define (compile-boolean=? e0 e1 c)
  (let ((c1 (compile-e e1 c))
        (c0 (compile-e e0 (cons #f c)))
        (l0 (gensym)))
    ;; FIXME this should really do the type check *after* both
    ;; expression have executed
    `(,@c1
      ,@assert-bool
      (mov (offset rsp ,(- (add1 (length c)))) rax)
      ,@c0
      ,@assert-bool
      (mov rbx ,imm-val-true)
      (cmp rax (offset rsp ,(- (add1 (length c)))))
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx)
      )))

(define (compile-cons? e0 c)
  (let ((c0 (compile-e e0 c))
        (l0 (gensym)))
    `(,@c0
      (mov rbx ,imm-val-true)
      (and rax #b111)
      (cmp rax ,type-pair)
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx))
    )
  )

(define (compile-empty? e0 c)
  (let ((c0 (compile-e e0 c))
        (l0 (gensym)))
    `(,@c0
      (mov rbx ,imm-val-true)
      (and rax #b11111)
      (cmp rax ,imm-type-empty)
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx))
    )
  )

(define (compile-box? e0 c)
  (let ((c0 (compile-e e0 c))
        (l0 (gensym)))
    `(,@c0
      (mov rbx ,imm-val-true)
      (and rax #b111)
      (cmp rax ,type-box)
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx))
    )
  )


(define (compile-= e0 e1 c)
  (let ((c1 (compile-e e1 c))
        (c0 (compile-e e0 (cons #f c)))
        (l0 (gensym)))
    ;; FIXME this should really do the type check *after* both
    ;; expression have executed
    `(,@c1
      ,@assert-integer
      (mov (offset rsp ,(- (add1 (length c)))) rax)
      ,@c0
      ,@assert-integer
      (mov rbx ,imm-val-true)
      (cmp rax (offset rsp ,(- (add1 (length c)))))
      (je ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx)
      )))

(define (compile-< e0 e1 c)
  (let ((c1 (compile-e e1 c))
        (c0 (compile-e e0 (cons #f c)))
        (l0 (gensym)))
    ;; FIXME this should really do the type check *after* both
    ;; expression have executed
    `(,@c1
      ,@assert-integer
      (mov (offset rsp ,(- (add1 (length c)))) rax)
      ,@c0
      ,@assert-integer
      (mov rbx ,imm-val-true)
      (cmp rax (offset rsp ,(- (add1 (length c)))))
      (jl ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx)
      )))

(define (compile-<= e0 e1 c)
  (let ((c1 (compile-e e1 c))
        (c0 (compile-e e0 (cons #f c)))
        (l0 (gensym)))
    ;; FIXME this should really do the type check *after* both
    ;; expression have executed
    `(,@c1
      ,@assert-integer
      (mov (offset rsp ,(- (add1 (length c)))) rax)
      ,@c0
      ,@assert-integer
      (mov rbx ,imm-val-true)
      (cmp rax (offset rsp ,(- (add1 (length c)))))
      (jle ,l0)
      (mov rbx ,imm-val-false)
      ,l0
      (mov rax rbx)
      )))

;; TODO: You'll need to add something to this
;; Any -> Boolean
(define (type-pred? x)
  (memq x '(integer?
            char?
            empty?
            boolean?
            box?
            cons?
            string?)))

;; Imm -> Asm
(define (compile-imm i)
  `((mov rax ,(imm->bits i))))

;; Imm -> Integer
(define (imm->bits i)
  (match i
    [(? integer? i) (arithmetic-shift i imm-shift)]
    [(? char? c)    (+ (arithmetic-shift (char->integer c) imm-shift) imm-type-char)]
    [(? boolean? b) (if b imm-val-true imm-val-false)]
    ['()            imm-type-empty]))








    



;; Variable CEnv -> Asm
(define (compile-var x c)
  (let ((i (lookup x c)))
    `((mov rax (offset rsp ,(- (add1 i)))))))

;; Expr CEnv -> Asm
(define (compile-box e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      (mov (offset rdi 0) rax)
      (mov rax rdi)
      (or rax ,type-box)
      (add rdi 8)))) ; allocate 8 bytes

;; Expr CEnv -> Asm
(define (compile-unbox e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      ,@assert-box
      (xor rax ,type-box)
      (mov rax (offset rax 0)))))

;; Expr Expr CEnv -> Asm
(define (compile-cons e0 e1 c)
  (let ((c0 (compile-e e0 c))
        (c1 (compile-e e1 (cons #f c))))
    `(,@c0
      (mov (offset rsp ,(- (add1 (length c)))) rax)
      ,@c1
      (mov (offset rdi 0) rax)
      (mov rax (offset rsp ,(- (add1 (length c)))))
      (mov (offset rdi 1) rax)
      (mov rax rdi)
      (or rax ,type-pair)
      (add rdi 16))))

;; Expr CEnv -> Asm
(define (compile-car e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      ,@assert-pair
      (xor rax ,type-pair) ; untag
      (mov rax (offset rax 1)))))

;; Expr CEnv -> Asm
(define (compile-cdr e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      ,@assert-pair
      (xor rax ,type-pair) ; untag
      (mov rax (offset rax 0)))))

;; Expr CEnv -> Asm
(define (compile-add1 e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      ,@assert-integer
      (add rax ,(arithmetic-shift 1 imm-shift)))))

;; Expr CEnv -> Asm
(define (compile-sub1 e0 c)
  (let ((c0 (compile-e e0 c)))
    `(,@c0
      ,@assert-integer
      (sub rax ,(arithmetic-shift 1 imm-shift)))))

;; Expr CEnv -> Asm
(define (compile-zero? e0 c)
  (let ((c0 (compile-e e0 c))
        (l0 (gensym))
        (l1 (gensym)))
    `(,@c0
      ,@assert-integer
      (cmp rax 0)
      (mov rax ,imm-val-false)
      (jne ,l0)
      (mov rax ,imm-val-true)
      ,l0)))

;; Expr Expr Expr CEnv -> Asm
(define (compile-if e0 e1 e2 c)
  (let ((c0 (compile-e e0 c))
        (c1 (compile-e e1 c))
        (c2 (compile-e e2 c))
        (l0 (gensym))
        (l1 (gensym)))
    `(,@c0
      (cmp rax ,imm-val-false)
      (je ,l0)
      ,@c1
      (jmp ,l1)
      ,l0
      ,@c2
      ,l1)))

;; Expr Expr CEnv -> Asm
(define (compile-+ e0 e1 c)
  (let ((c1 (compile-e e1 c))
        (c0 (compile-e e0 (cons #f c))))
    ;; FIXME this should really do the type check *after* both
    ;; expression have executed
    `(,@c1
      ,@assert-integer
      (mov (offset rsp ,(- (add1 (length c)))) rax)
      ,@c0
      ,@assert-integer
      (add rax (offset rsp ,(- (add1 (length c))))))))

;; Variable CEnv -> Natural
(define (lookup x cenv)
  (match cenv
    ['() (error "undefined variable:" x)]
    [(cons y cenv)
     (match (eq? x y)
       [#t (length cenv)]
       [#f (lookup x cenv)])]))

(define (assert-type p)
  `((mov rbx rax)
    (and rbx ,(type-pred->mask p))
    (cmp rbx ,(type-pred->tag p))
    (jne err)))

;; TypePred -> Integer
(define (type-pred->mask p)
  (match p
    [(or 'box? 'cons? 'string?) result-type-mask]
    [_ imm-type-mask]))

;; TypePred -> Integer
(define (type-pred->tag p)
  (match p
    ['box?     type-box]
    ['cons?    type-pair]
    ['string?  type-string]
    ['integer? imm-type-int]
    ['empty?   imm-type-empty]
    ['char?    imm-type-char]
    ['boolean? imm-type-bool]))


(define assert-integer (assert-type 'integer?))
(define assert-box     (assert-type 'box?))
(define assert-pair    (assert-type 'cons?))
(define assert-char    (assert-type 'char?))
(define assert-bool    (assert-type 'boolean?))
(define assert-string    (assert-type 'string?))

;;(compile-e (prim-e (list 'box? (prim-e 'unbox (list (prim-e 'box (list (int-e 8)))))) '()) '())