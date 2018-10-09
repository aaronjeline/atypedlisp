#lang racket

(struct native (def))
(struct typedef (params result) #:transparent)
(struct adt (name params) #:transparent)
(struct typevar (name) #:transparent)

(define avail-types '(boolean number string list any))

(define (->number n)
  (if (number? n) n
      (error (format "Cast Error: Can't case ~a to number" n))))

(define type-data
  (list (cons '+ (typedef '(number number) 'number))
        (cons '= (typedef '(number number) 'boolean))
        (cons 'sub1 (typedef '(number) 'number))
        (cons 'or (typedef '(boolean boolean) 'boolean))
        (cons 'cons (typedef '(any list) 'list))
        (cons 'car (typedef '(list) 'any))
        (cons 'cdr (typedef '(list) 'list))
        (cons 'and (typedef '(boolean boolean) 'boolean))
        (cons '* (typedef '(number number) 'number))
        (cons 'add1 (typedef '(number) 'number))
        (cons '->number (typedef '(any) 'number))))
  

(define init-env 
  (list (cons '+ (native +))
        (cons '= (native =))
        (cons '* (native *))
        (cons 'and '(λ (x y) (if x (if y #t #f) #f)))
        (cons 'or '(λ (x y) (if x #t (if y #t #f))))
        (cons 'add1 '(λ (x) (+ x 1)))
        (cons 'sub1 (native sub1))
        (cons 'cons (native cons))
        (cons 'car (native car))
        (cons 'cdr (native cdr))
        (cons '->number (native ->number))))




(define (READ str)
  (read (open-input-string (string-append "(begin " str ")"))))

(define (EVAL ast env) 
  (match ast
    ['() '()]
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
    [(cons 'struct rst)
     (create-struct (cons 'struct rst))]
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
  (let* [(parsed (READ source))
         (annos (filter typeanno? parsed))
         (evals (filter-not typeanno? parsed))]
    (begin
      (if (andmap typecheck (rest evals))
          (PRINT (EVAL evals init-env))
          (error "Typecheck failed")))))

(define (typeanno? e)
  (match e
    [(cons ': r) #t]
    [else #f]))

(define (proc-anno anno)
  (match anno
    [(list ': name types '-> result) #:when (list? types)
                                     (set! type-data
                                           (cons
                                            (cons name
                                                  (typedef types result))
                                            type-data))]
    [(list ': name type '-> result) #:when (symbol? type)
                                     (set! type-data
                                           (cons
                                            (cons name
                                                  (typedef (list type) result))
                                            type-data))]
    [else (error "Bad type annotation!")]))

(define (typedef-eq? a b)
  (and (andmap (λ (c) (eq? (car c) (cdr c))) (map cons (typedef-params a)
                                                  (typedef-params b)))
       (eq? (typedef-result a) (typedef-result b))))

(define (matches-anno type name)
  (let* [(lookup (assv name type-data))]
    (if (not (false? lookup))
        (typedef-eq? type (cdr lookup))
        #t)))

(define (typecheck ast)
  (match ast
    [(cons 'quote e) #t]
    [(cons 'begin forms)
     (andmap typecheck forms)]
    [(list 'if con if-true if-false)
     (and (eq? 'boolean (result-type con))
          (eq? (result-type if-true) (result-type if-false)))]
    [(list 'define (cons f args) body)
     (let* [(eqλ `(λ ,args ,body))]
       (if (and (typecheck eqλ) (matches-anno (λtype eqλ) f))
           (set! type-data (cons (cons f (λtype eqλ)) type-data))
           #f))]
    [(list 'define sym val)
     (if (typecheck val)
         (set! type-data (cons (cons sym (result-type val)) type-data))
         #f)]
    [(list 'struct name parts)
     (if (not (valid-struct-parts parts))
         (error "Invalid struct defition" (list 'struct name parts))
         (begin
           (set! avail-types (cons name avail-types))
           (let* [(types (field-types parts))]
             (set! type-data (append (list (cons name (typedef types name)))
                                     (map (λ (x) (build-asc-types name x)) parts)
                                     type-data)))
           #t))]
                                                   
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
       (if (false? type) (error (format "Function ~a has no type data" f))
           (cond [(not (andmap typecheck args)) (error "Sub-expr failed typecheck")]
                 [(not (= (length (typedef-params type)) (length args)))
                  (error (format "Wrong number of arguments for ~a: expected ~a, found ~a"
                                 f (length (typedef-params type)) (length args)))]
                 [(not (andmap same-pair?
                               (map cons (typedef-params type) (map result-type args))))
                  (mismatch-error f type args)]
                 [else #t])))]
    [(? symbol?) #t]
    [(? atom?) #t]))

(define (mismatch-error f type args)
  (let* [(misms (filter-not (λ (l) (eq? (first l) (second l)))
                            (map list
                                 (typedef-params type)
                                 (map result-type args)
                                 (range 0 (length args)))))
         (errs (map (λ (m) (format "Argument #~a, expected ~a, found ~a"
                                   (third m)
                                   (first m)
                                   (second m))) misms))
         (comb (foldr string-append "\n" errs))]
    (error (string-append (format "In function ~a:" f) comb))))
                                   

(define (λtype func)
  (match func
    [s #:when (symbol? s) (cdr (assv s type-data))]
    [(list 'λ args body)
     (let [(arg-types (map (λ (a) (find-arg-expr a body)) args))]
       (cond [(ormap empty? arg-types) (error "Unused paramter in function")]
             [(andmap all-list? arg-types)
              (typedef (map first arg-types) 
                       (result-type body))]
             [else #f]))]))
    
(define (all-list? lst)
  (if (empty? lst) #t
      (foldr (λ (n sf) (and n (eq? n (first lst)))) #t (rest lst))))
     
(define (find-arg-expr arg body)
  (match body
    [(cons f args)
     (append #;(handle-arg-f f args arg)
             (handle-arg-arg f args arg)
             (apply append (map (λ (e) (find-arg-expr arg e)) args)))]
    [else '()]))

#;(define (handle-arg-f f args arg)
  (if (eq? f arg)))
      

(define (handle-arg-arg f args arg)
  (if (ormap (λ (x) (eq? x arg)) args)
      (list (list-ref (typedef-params (λtype f)) (index-of args arg)))
      '()))
     

  
(define (result-type val)
  (match val
    ['() 'list]
    [(list 'quote v) (result-type v)]
    [n #:when (number? n) 'number]
    [s #:when (string? s) 'string]
    [b #:when (boolean? b) 'boolean]
    [s #:when (symbol? s)
       (match (cdr (assv s type-data))
         [(typedef params result) result]
         [type type])]
    [(list 'if _ a b) (result-type a)]
    [(cons 'begin forms) (result-type (last forms))]
    [(cons f args) (typedef-result (cdr (assv f type-data)))]))
    
(define (same-pair? p)
  (or (eq? (car p) (cdr p))
      (eq? (car p) 'any)))


(define (fapply func args oenv)
  (match func
    [(list 'λ params body)
     (EVAL body (append (map cons params args) oenv))]
    [else (error "Attempted function application on non-function value")]))

(define (atom? x)
  (or (number? x) (boolean? x) (string? x) (native? x)))

(define (create-struct sd)
  (match sd
    [(list 'struct name parts)
     (let* [(p-names (part-names parts))]
       (begin
         (eval `(struct ,name ,p-names #:transparent))
         (set! init-env (append (list (cons name (native (eval name))))
                                (map (λ (acc) (cons acc (native (eval acc)))) (build-accessors name p-names))
                                init-env))))]))

(define (part-names parts)
  (map (λ (part)
         (match part
           [(list name ': type) name])) parts))

(define (field-types fields)
  (map (λ (part)
         (match part
           [(list name ': type) type])) fields))

(define (build-accessor sname part)
  (string->symbol (string-append (symbol->string sname)
                                 "-"
                                 (symbol->string part))))

(define (build-accessors sname parts)
  (map (λ (x) (build-accessor sname x)) parts))

(define (build-asc-types sname asc)
  (match asc
    [(list fname ': type)
     (cons (build-accessor sname fname) (typedef (list sname) type))]))

                         
(define (valid-struct-parts parts)
  (andmap (λ (part)
            (match part
              [(list name ': type) #:when (member type avail-types) #t]
              [else #f])) parts))

(define (last lst)
  (match lst
    [(cons a '()) a]
    [(cons a b) (last b)]))
