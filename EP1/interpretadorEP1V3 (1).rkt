#lang plai-typed

#|
 | interpretador simples, sem variáveis ou funçõess
 |#

#| primeiro as expressões "primitivas", ou seja, diretamente interpretadas
 |#

(define-type ExprC
  [emptyC]
  [numC    (n : number)]
  [idC     (s : symbol)]
  [plusC   (l : ExprC) (r : ExprC)]
  [multC   (l : ExprC) (r : ExprC)]
  [lamC    (arg : symbol) (body : ExprC)]
  [appC    (fun : ExprC) (arg : ExprC)]
  [ifC     (cond : ExprC) (y : ExprC) (n : ExprC)]
  [consC   (car : ExprC) (cdr : ExprC)]; Creates cell with a pair
  [carC    (pair : ExprC)]; Gets 1st element of a pair
  [cdrC    (pair : ExprC)]; Gets 2nd element of a pair
  [seqC    (body : (listof ExprC))]
  [setC (s : symbol) (val : ExprC)]
  [letC (name : symbol) (arg : ExprC) (body : ExprC)]
  [let*C (args : (listof symbol)) (funcs : (listof ExprC)) (exp : ExprC)]
  [quoteC (s : symbol)]
  )
#| agora a linguagem aumentada pelo açúcar sintático
 | neste caso a operação de subtração e menus unário
 |#

(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)]
  [lamS    (arg : symbol) (body : ExprS)]
  [appS    (fun : ExprS) (arg : ExprS)]
  [plusS   (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [consS   (car : ExprS) (cdr : ExprS)]
  [carS    (pair : ExprS)]
  [cdrS    (pair : ExprS)]
  [seqS    (body : (listof ExprS))]
  [setS    (s : symbol) (val : ExprS)]
  [letS    (name : symbol) (arg : ExprS) (body : ExprS)]
  [let*S   (args : (listof symbol)) (funcs : (listof ExprS)) (exp : ExprS)]
  [letrecS (arg : symbol) (func : ExprS) (exp : ExprS)]
  [quoteS  (s : symbol)]
  )


(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS    (n)        (numC n)]
    [idS     (s)        (idC s)]
    [lamS    (a b)      (lamC a (desugar b))]
    [appS    (fun arg)  (appC (desugar fun) (desugar arg))]
    [plusS   (l r)      (plusC (desugar l) (desugar r))]
    [multS   (l r)      (multC (desugar l) (desugar r))]
    [bminusS (l r)      (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)        (multC (numC -1) (desugar e))]
    [ifS     (c y n)    (ifC (desugar c) (desugar y) (desugar n))]
    [consS   (b1 b2)    (consC (desugar b1) (desugar b2))]
    [carS    (c)        (carC (desugar c))]
    [cdrS    (c)        (cdrC (desugar c))]
    [seqS (body) (seqC (cons (desugar (first body))
                             (cond
                               [(not (empty? (rest body))) (cons (desugar (second body)) empty)]
                               [else empty]
                               )
                             ))]
    [setS (sym val) (setC sym (desugar val))]
    [letS (name arg body) (letC name (desugar arg) (desugar body))]
    [let*S (args funcs exp) (let*C args (list (desugar (first funcs)) (desugar (second funcs))) (desugar exp))]
    [letrecS (arg fun exp) (letC arg (emptyC) (seqC (cons (setC arg (desugar fun)) (cons (desugar exp) empty))))]
    [quoteS  (s)             (quoteC s)]
    ))



; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  [symV (s : symbol)]
  [closV (arg : symbol) (body : ExprC) (env : Env)]
  [consV (car : Value) (cdr : Value)]
 
  )


; Bindings associate symbol with Boxes
; we need this to be able to change the value of a binding, which is important
; to implement letrec.

(define-type Binding
        [bind (name : symbol) (val : (boxof Value))])


; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)


; Storage's operations are similar to Env's
;   bind <-> cell
;   mt-env <-> mt-store
;   extend-env <-> override-store


; lookup changes its return type
(define (lookup [varName : symbol] [env : Env]) : (boxof Value); lookup returns the box, we need this to change the value later
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string varName) " não foi encontrado"))] ; livre (não definida)
            [else (cond
                    [(symbol=? varName (bind-name (first env)))   ; achou!
                     (bind-val (first env))]
                    [else (lookup varName (rest env))])]))        ; vê no resto



; Primitive operators
(define (num+ [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "Um dos argumentos não é número")]))

(define (num* [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "Um dos argumentos não é número")]))


; Return type for the interpreter, Value


(define (interp [a : ExprC] [env : Env] ) : Value
  (type-case ExprC a
    [emptyC () (symV '_)]
    [numC (n) (numV n) ]
    [idC (n)  (unbox (lookup n env))]; we need to unbox the value in the environment before using it
    [lamC (a b) (closV a b env) ]

 
    ; application of function
    [appC (f a)
          (let ((closure (interp f env))
                (argvalue (interp a env)))
            (type-case Value closure
              [closV (parameter body env)
                     (interp body (extend-env (bind parameter (box argvalue)) env))]
              [else (error 'interp "operation app aplied to non-closure")]
              ))]
   
    ;I left plusC without error-checking
    [plusC (l r)
             (let ((left (interp l env))
                   (right (interp r env)))
               (num+ left right))]
    ;multC
    [multC (l r)
           (let ( (left (interp l env))
                  (right (interp r env)))
             ;in this case type cheking is a little different
             (if (numV? left)
                 (if (numV? right)
                     (num* left right)
                     (error 'interp "second argument of multiplication not a number value"))
                 (error 'interp "first argument of multiplication not a number value"))
                 )]
    ; ifC serializes
    [ifC (c s n) (type-case Value (interp c env)
                   [numV (value)
                        (if (zero? value)
                            (interp n env )
                            (interp s env ))]
                   [else (error 'interp "condition not a number")]
                   )]

    ; Working with lists
    [consC (b1 b2) (let ( (car (interp b1 env))
                          (cdr (interp b2 env)))
                     (consV car cdr))]
    [carC (c) (type-case Value (interp c env)
                [consV (car cdr)
                       car]
                [else (error 'interp "car applied to non-cell")]
                )]
    [cdrC (c) (type-case Value (interp c env)
                [consV (car cdr)
                       cdr]
                [else (error 'interp "cdr applied to non-cell")]
                )]

    [setC (sym val)
          (local ([define current (lookup sym env)])
            (begin
              (set-box! current (interp val env))
              (unbox current)
              )
            )]
    [seqC (body) (if (empty? (rest body)) (interp (first body) env) (begin (interp (first body) env) (interp (second body) env)))]
    [letC (name arg body)
          (let* ([new-bind (bind name (box (interp arg env)))]
                 [new-env (extend-env new-bind env)])
            (interp body new-env)
            )]
    [let*C (args funcs exp)  
           (local ([define first-env (extend-env (bind (first args) (box (interp (first funcs) env))) env)])
             (local ([define second-env (extend-env (bind (second args) (box (interp (second funcs) first-env))) first-env)])
               (interp exp second-env)
               ))]

    
    [quoteC (s) (symV s)]

    ))
  

; Parser with funny instructions for boxes
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))] ; pode ser um símbolo livre nas definições de função
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         [(lambda) (lamS (s-exp->symbol (second sl)) (parse (third sl)))] ; definição
         [(call) (appS (parse (second sl)) (parse (third sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(cons) (consS (parse (second sl)) (parse (third sl)))]
         [(car) (carS (parse (second sl)))]
         [(cdr) (cdrS (parse (second sl)))]
         [(seq) (seqS (cons (parse (second sl))
                            (cond
                              [(not (empty? (rest (rest sl)))) (cons (parse (list->s-exp (cons (symbol->s-exp 'seq) (rest (rest sl))))) empty)]
                              [else empty]
                              )
                            ))]
         [(set) (setS (s-exp->symbol (second sl)) (parse (third sl)))]
         [(let) (letS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                      (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                      (parse (third sl)))]
         [(let*) (let*S (list (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl)))))) (s-exp->symbol (first (s-exp->list (second (s-exp->list (second sl)))))))
                        (list (parse (second (s-exp->list (first (s-exp->list (second sl)))))) (parse (second (s-exp->list (second (s-exp->list (second sl)))))))
                        (parse (third sl))
                        )]
         [(letrec) (letrecS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                            (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                            (parse (third sl)))]
         [(quote) (quoteS (s-exp->symbol (second sl)))]
         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) mt-env))


; Examples
(interpS '(+ 10 (call (lambda x (car x)) (cons 15 16))))

(interpS '(call (lambda x (+ x 5)) 8))


(interpS '(call (lambda f (call f (~ 32))) (lambda x (- 200 x))))


; Tests
(test (interp (carC (consC (numC 10) (numC 20)))
              mt-env)
      (numV 10))

; testando let
(test (interpS '(let ([x 10]) (+ x x)))
      (numV 20))

; testando let*
(test (interpS '(let* ([x 10]  [y 20]) (+ x y)))
      (numV 30))

; testando letrec
(test (interpS '(letrec ([fac (func n (if n (* n (call fac (- n 1))) 1))])
                  (call fac 5)))
      (numV 120))
