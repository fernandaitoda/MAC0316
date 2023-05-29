#lang plai-typed

;Nome: Eike Souza da Silva 4618653
;Nome: Fernanda Itoda 10740825

#|
 | interpretador simples, com variáveis e funções
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
  [letrecC (var : symbol) (expression : ExprC) (body : ExprC)]
  [quoteC  (sym : symbol)]
  [equalC (exp1 : ExprC) (exp2 : ExprC)]
  )
#| agora a linguagem aumentada pelo açúcar sintático
 | neste caso a operação de subtração e menus unário
 |#

(define-type ExprS
  [emptyS]
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
  [letS    (var : symbol) (exp : ExprS) (body : ExprS)]
  [let*S    (var1 : symbol) (exp1 : ExprS) (var2 : symbol) (exp2 : ExprS) (body : ExprS)]
  [letrecS (var : symbol)  (exp : ExprS)  (body : ExprS)]
  [quoteS  (sym : symbol)]
  [equalS (exp1 : ExprS) (exp2 : ExprS)]
  )


(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [emptyS () (emptyC)]
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
    [letS    (v e b)    (appC (lamC v (desugar b)) (desugar e))]
    [let*S    (v1 e1 v2 e2 b)    (appC (lamC v1 (appC (lamC v2 (desugar b) )
                                                      (desugar e2)))
                                       (desugar e1))]
    [letrecS    (v e  b)  (letrecC v (desugar e) (desugar b))]
    [quoteS  (sym) (quoteC sym)]
    [equalS (exp1 exp2) (equalC (desugar exp1) (desugar exp2))]

    ))



; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  [closV (arg : symbol) (body : ExprC) (env : Env)]
  [consV (car : Value) (cdr : Value)]
  [symV (sym : symbol)]
  [suspV (expr : ExprC) (env : Env)]
  [boolV (sym : boolean)]
  [addressV (id : number)]
  )

(define-type Result
      [v*s (v : Value) (s : Store)])

(define-type Promise
      [aPromise (valueBox : (boxof Value))])

; Bindings associate symbol with Boxes
; we need this to be able to change the value of a binding, which is important
; to implement letrec.

(define-type Binding
        [bind (name : symbol) (val : number)])

; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)


; Storage's operations are similar to Env's
;   bind <-> cell
;   mt-env <-> mt-store
;   extend-env <-> override-store
(define-type Storage
  [cell (location : number) (val : (boxof Value))])
(define-type-alias Store (listof Storage))
(define mt-store empty)
(define override-store cons)

; lookup changes its return type
(define (lookup [varName : symbol] [env : Env]) : number
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string varName) " não foi encontrado"))] ; livre (não definida)
            [else (cond
                    [(symbol=? varName (bind-name (first env)))   ; achou!
                     (bind-val (first env))]
                    [else (lookup varName (rest env))])]))        ; vê no resto


; fetch is equivalent to a lookup for the store
; find the box of a variable in an store
(define (fetch [for : number] [store : Store]) : (boxof Value)
  (cond
    [(empty? store) (error 'fetch (string-append (to-string for) " was not found"))]
    [else (cond
            [(= for (cell-location (first store)))   
             (cell-val (first store))]
            [else (fetch for (rest store))]
            )]
    )
  )

; Returns the next location available
(define new-loc
   (let ( [ n (box 0)])
        (lambda () 
           (begin
              (set-box! n (+ 1 (unbox n)))
              (unbox n)))))


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


(define (evalSusp [susp-box : (boxof Value)] [store : Store]) : Result
  (let ([eval-result (interp (suspV-expr (unbox susp-box)) (suspV-env (unbox susp-box)) store)])
    (begin
      (set-box! susp-box (v*s-v eval-result))
      eval-result
      )
    )
  )

; Return type for the interpreter, Value


(define (interp [a : ExprC] [env : Env] [store : Store]) : Result
  (type-case ExprC a
    [numC (n) (v*s (numV n) store)]
    [idC (n)
         (let ([address (lookup n env)])
           (type-case Value (unbox (fetch address store))
             [suspV (body env)
                    (evalSusp (fetch address store) store)]
             [else (v*s (unbox (fetch address store)) store)]
             ))]
    
    [lamC (a b) (v*s (closV a b env) store)]

 
    ; application of function
    [appC (f a)
          (type-case Result (interp f env store)
            [v*s (value-f store-f)
                  (let ([currentLocation (new-loc)])
                    (interp (closV-body value-f)
                            (extend-env (bind (closV-arg value-f) currentLocation) (closV-env value-f))
                            (override-store (cell currentLocation (box (suspV a env))) store-f)
                            )
                    )]
            )]
   
    ;I left plusC without error-checking
    [plusC (l r)
           (type-case Result (interp l env store)
             [v*s (value-l store-l)
                   (type-case Result (interp r env store)
                     [v*s (value-r store-r) (v*s (num+ value-l value-r) store-r)]
                     )]             
             )]
    ;multC
    [multC (l r)
           (type-case Result (interp l env store)
             [v*s (value-l store-l)
                   (type-case Result (interp r env store)
                     [v*s (value-r store-r) (v*s (num* value-l value-r) store-r)]
                     )]             
             )]

    [equalC (exp1 exp2)
            (let* ([left (interp exp1 env store)] [right (interp exp2 env (v*s-s left))])
              (if (equal? (v*s-v left) (v*s-v right)) (v*s (boolV #t) (v*s-s right)) (v*s (boolV #f) (v*s-s right)))
              )]

    [emptyC () (v*s (symV '_) store)]
    
    ; ifC serializes
    [ifC (c s n)
         (let ([condition (interp c env store)])
           (cond
             [(boolV? (v*s-v condition)) (if (not (boolV-sym (v*s-v condition))) (interp n env (v*s-s condition)) (interp s env (v*s-s condition)))]
             [else (if (zero? (numV-n (v*s-v condition))) (interp n env (v*s-s condition)) (interp s env (v*s-s condition)))]
             )
           )]

    ; Working with lists
    [consC (car cdr)
           (let* ([firstLocation (new-loc)]
                  [secondLocation (new-loc)]
                  [first-store (override-store (cell firstLocation (box (suspV car env))) store)]
                  [second-store (override-store (cell secondLocation (box (suspV cdr env))) first-store)])
             (v*s (consV (addressV firstLocation) (addressV secondLocation)) second-store)
             )]
    [carC  (exp)
           (let* ([list-result (interp exp env store)]
                  [exp-box (fetch (addressV-id (consV-car (v*s-v list-result))) (v*s-s list-result))])
             (cond
               [(suspV? (unbox exp-box)) (let ([exp-interp (interp (suspV-expr (unbox exp-box)) (suspV-env (unbox exp-box)) (v*s-s list-result))])
                          (begin
                            (set-box! exp-box (v*s-v exp-interp))
                            exp-interp
                            ))]
               [else (v*s (unbox exp-box) (v*s-s list-result))]
               ))]
    [cdrC  (exp)
           (let* ([exp-result (interp exp env store)]
                  [exp-box (fetch (addressV-id (consV-cdr (v*s-v exp-result))) (v*s-s exp-result))])
             (cond
               [(suspV? (unbox exp-box)) (let ([exp-interp (interp (suspV-expr (unbox exp-box)) (suspV-env (unbox exp-box)) (v*s-s exp-result))])
                          (begin
                            (set-box! exp-box (v*s-v exp-interp))
                            (v*s (unbox exp-box) (v*s-s exp-interp))
                            ))]
               [else (v*s (unbox exp-box) (v*s-s exp-result))]
               ))]
  
    [letrecC (sym arg exp)
             (let* ([currentLocation (new-loc)]
                    [new-env (extend-env (bind sym currentLocation) env)]
                    [new-arg (interp (emptyC) env store)]
                    [new-store (override-store (cell currentLocation (box (v*s-v new-arg))) (v*s-s new-arg))]
                    [b (fetch (lookup sym new-env) new-store)])
               (begin (set-box! b (suspV arg new-env)) (interp exp new-env new-store))
               )]
                 
    [quoteC  (s) (v*s (symV s) store)]
 

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
         [(quote) (quoteS (s-exp->symbol (second sl)))]
         [(let) (letS (s-exp->symbol (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(let*) (let*S (s-exp->symbol (second sl))
                        (parse (third sl))
                        (s-exp->symbol (fourth sl))
                        (parse (fourth (rest sl)))
                        (parse (fourth (rest (rest sl)))))]
         [(let) (letS (s-exp->symbol (second sl))
                      (parse (third sl))
                      (parse (fourth sl)))]
         [(letrec) (letrecS (s-exp->symbol (second sl))
                            (parse (third sl))
                            (parse (fourth sl)))]
         [(equal?) (equalS (parse (second sl)) (parse (third sl)))]    
     
        
         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) mt-env mt-store))


; Examples
(interpS '(+ 10 (call (lambda x (car x)) (cons 15 16))))

(interpS '(call (lambda x (+ x 5)) 8))


(interpS '(call (lambda f (call f (~ 32))) (lambda x (- 200 x))))


; Tests
; testando equal?
(test (interpS '(equal? 1 1)) (v*s (boolV #t) empty))

(test (interpS '(equal? 1 2)) (v*s (boolV #f) empty))

(test (interpS '(equal? (+ 4 2) (- 8 2))) (v*s (boolV #t) empty))

(test (interpS '(equal? (lambda x (+ x x)) (lambda y (+ y y))))
      (v*s (boolV #f) empty))
