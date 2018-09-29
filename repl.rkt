#lang racket

(struct native (def))
(struct typedef (params result) #:transparent)
(struct adt (name params) #:transparent)
(struct typevar (name) #:transparent)

(define type-data
  (list (cons '+ (typedef '(number number) 'number))
        (cons '= (typedef '(number number) 'boolean))
        (cons 'sub1 (typedef '(number) 'number))
        (cons 'and (typedef '(boolean boolean) 'boolean))))
  

(define init-env 
  (list (cons '+ (native +))
        (cons '= (native =))
        (cons '* (native *))
        (cons 'and '(λ (x y) (if x (if y #t #f) #f)))
        (cons 'sub1 (native sub1))
        (cons 'cons (native cons))
        (cons 'car (native car))
        (cons 'cdr (native cdr))))



(define (READ str)
  (read (open-input-string (string-append "(begin " str ")"))))

(define (EVAL ast env) 
  (match ast
    [s #:when (symbol? s)
       (let* [(resolve (assv s env))]
         (if (not (pair? resolve))
             (error "Undefined symbol:" s)
             (cdr resolve)))]
    [a #:when (atom? a) a]
    [(cons 'begin exprs)
     (for/fold ([val void])
               ([expr exprs])
       (EVAL expr init-env))]
    [(cons 'quote rst) (first rst)]
    [(list 'λ args body) (list 'λ args body)]
    [(list 'let bind expr)
     (match bind
       [(list sym val)
        (EVAL expr (cons (cons sym (EVAL val env)) env))])]
    [(list 'define (cons f args) body)
     (EVAL `(define ,f (λ ,args ,body)) env)]
    [(list 'define sym val)
     (set! init-env (cons (cons sym (EVAL val env)) init-env))]
    [(list 'if dec t f) (if (EVAL dec env)
                            (EVAL t env)
                            (EVAL f env))]
    [l #:when (list? l)
       ;; Function application
       (let* [(evald (map (λ (s) (EVAL s env)) l))]
         (match evald
           [(cons func args) #:when (native? func)
                             (apply (native-def func) args)]
           [(cons func args) (fapply func args env)]))]))

(define (PRINT ast) 
  (match ast
    [void void]
    [n #:when (number? n) (number->string n)]
    [s #:when (string? s) s]
    [b #:when (boolean? b) (if b "#t" "#f")]
    [n #:when (native? n) "<native-function>"]
    [(list 'λ args body) "<λfunction>"]
    [(cons fst rst) (string-append
                     "("
                     (foldr (λ (sa r) (string-append (PRINT sa) " " r))
                            ")"
                            (cons fst rst)))]))

(define (rep source)
  (let* [(parsed (READ source))]
    (if (andmap typecheck (rest parsed))
        (PRINT (EVAL parsed init-env))
        (error "Typecheck failed"))))

(define (typecheck ast)
  (match ast
    [(list 'if con if-true if-false)
     (and (eq? 'boolean (result-type con))
          (eq? (result-type if-true) (result-type if-false)))]
    [(list 'define (cons f args) body)
     (let* [(eqλ `(λ ,args ,body))]
       (if (typecheck eqλ)
           (set! type-data (cons (cons f (λtype eqλ)) type-data))
           #f))]
    [(list 'define sym val)
     (if (typecheck val)
         (set! type-data (cons (cons sym (result-type val)) type-data))
         #f)]
    [(list 'λ args body)
     (not (false? (λtype (list 'λ args body))))]
    [(cons (cons 'λ rst) args)
     (let* [(type (λtype (cons 'λ rst)))]
       (and (not (false? type))
            (andmap typecheck args)
            (= (length (typedef-params type)) (length args))
            (andmap same-pair? (map cons(typedef-params type) (map result-type args)))))]
    [(cons f args)
     (let* [(type (cdr (assv f type-data)))]
       (and (andmap typecheck args)
            (= (length (typedef-params type)) (length args))
            (andmap same-pair? (map cons (typedef-params type) (map result-type args)))))]
    [(? symbol?) #t]
    [(? atom?) #t]))

(define (λtype func)
  (match func
    [s #:when (symbol? s) (cdr (assv s type-data))]
    [(list 'λ args body)
     (let [(arg-types (map (λ (a) (find-arg-expr a body)) args))]
       (if (andmap all-list? arg-types)
           (typedef (map first arg-types) 
                    (result-type body))
           #f))]))
    
(define (all-list? lst)
  (or (= 1 (length lst))
      (apply eq? lst)))
     
(define (find-arg-expr arg body)
  (match body
    [(cons f args) #:when (ormap (λ (x) (eq? x arg)) args)
                   (cons (list-ref (typedef-params (λtype f)) (index-of args arg))
                         (apply append (map (λ (e) (find-arg-expr arg e)) args)))]
    [(cons f args) (apply append (map (λ (e) (find-arg-expr arg e)) args))]
    [else '()]))
     

  
(define (result-type val)
  (match val
    [n #:when (number? n) 'number]
    [s #:when (string? s) 'string]
    [b #:when (boolean? b) 'boolean]
    [s #:when (symbol? s)
       (match (cdr (assv s type-data))
         [(typedef params result) result]
         [type type])]
    [(list 'if _ a b) (result-type a)]
    [(cons f args) (typedef-result (cdr (assv f type-data)))]))
    
(define (same-pair? p)
  (or (eq? (car p) (cdr p))
      (eq? 'any (car p))
      (eq? 'any (cdr p))))

(define (fapply func args oenv)
  (match func
    [(list 'λ params body)
     (EVAL body (append (map cons params args) oenv))]
    [else (error "Attempted function application on non-function value")]))

(define (atom? x)
  (or (number? x) (boolean? x) (string? x) (native? x)))
