#lang curly-fn sweet-exp racket

(require racket/block)
(require racket/match)
(require racket/pretty)
(require racket/serialize)

(require data/gvector)

(module structures racket
  (require racket/serialize)
  (provide (all-defined-out))
  
  (serializable-struct environment (parent defs))
  
  (define (make-env parent (init '()))
    (define defs (make-hash init))
    (hash-for-each defs #{hash-set! defs %1 (box %2)})
    (environment parent defs))
  
  (define (stat-env-getbox env name)
    (when (eq? env 'none) (raise-user-error (format "no such name ~A" name)))
    (let* ([nope (gensym)]
           [result (hash-ref (environment-defs env) name nope)])
      (if (eq? result nope)
          (stat-env-getbox (environment-parent env) name)
          result)))
  
  (define (stat-env-ref env name)
    (unbox (stat-env-getbox env name)))
  
  (define (stat-env-set! env name value)
    (set-box! (stat-env-getbox env name) value)
    value)
  
  (define (stat-env-new! env name value)
    (hash-set! (environment-defs env) name (box value))
    value)
  
  (define (stat-env-del! env name)
    (when (eq? env 'none) (raise-user-error (format "no such name ~A" name)))
    (define defs (environment-defs env))
    (if (hash-has-key? defs name)
        (hash-remove! defs name)
        (stat-env-del! (environment-parent env) name)))
  
  (serializable-struct special (item))
  
  (serializable-struct subprogram (static-parent-env formals body))
  
  (serializable-struct rewriter (definition-site-env formals body))
  )

(require 'structures)

(define debug (make-parameter #f))

(define PATH (build-path (current-directory) "ss-save.txt"))

(define (start)
  (define env (deserialize (read (open-input-file PATH #:mode 'text))))
  (define defs (environment-defs env))
  (hash-for-each (environment-defs (make-start-env))
                 #{hash-set! defs %1 %2})
  (main env))

(define (start-blank)
  (main (make-start-env)))

(define (start-debug)
  (parameterize ([debug #t])
    (start)))

(define (main global-env)
  (let/ec quit
    (let loop ()
      (display "ss> ")
      (let ([line (read-line)])
        (unless (eof-object? line)
          (with-handlers
              ([exn:fail:user? #{displayln (exn-message %)}]
               [exn:quit? #{quit}])
            (process global-env line))
          (loop)))))
  (with-output-to-file PATH #:mode 'text #:exists 'replace
    #{write (serialize global-env)}))

(struct exn:quit exn ())
(define (raise-quit)
  (raise (exn:quit "user quit" (current-continuation-marks))))

(define (process env line)
  (define command (parse line))
  (define result (evaluate env command))
  (unless (void? result) (writeln result)))

(define (parse line)
  (with-handlers
      ([exn:fail:read? #{raise-user-error (exn-message %)}])
    (read (open-input-string line))))

(define (evaluate env command)
  (define todos (list `#s(evaluate ,env ,command)))
  (define targets (list (make-gvector)))
  (when (debug) (pretty-columns todos targets))
  (match (evaluate-completely todos targets)
    [(list result-vec)
     (case (gvector-count result-vec)
       [(0) (void)]
       [(1) (gvector-ref result-vec 0)]
       [else (raise-user-error "bad result vector ~A"
                               (gvector->vector result-vec))])]
    [bad-targets (raise-user-error "bad result stack ~A"
                                   (map gvector->vector bad-targets))]))

(define (evaluate-completely todos targets)
  (match-define `#(,new-todos ,new-targets) (evaluate-step todos targets))
  (when (debug) (pretty-columns new-todos new-targets))
  (if (null? new-todos)
      new-targets
      (evaluate-completely new-todos new-targets)))

(define (pretty-columns . items)
  (let* [(converted-items (map convert-gvectors items))
         (pretty-items (map #{pretty-format % 40 #:mode 'display}
                            converted-items))
         (pretty-lineses (map #{string-split % "\n"} pretty-items))]
    (displayln (string-join (paste pretty-lineses) "\n"))
    (newline)))

(define/match (paste _)
  [(`(,this-lines ,that-lines . ,other-columns))
   (let* [(width (apply max (map string-length this-lines)))
          (this-length (length this-lines))
          (that-length (length that-lines))
          (max-length (max this-length that-length))
          (padded-this (map #{pad % width " | "} this-lines))
          (extended-this (append padded-this
                                 (make-list (- max-length this-length)
                                            (pad "" width " | "))))
          (extended-that (append that-lines
                                 (make-list (- max-length that-length) "")))]
     (paste (cons (map string-append extended-this extended-that)
                  other-columns)))]
  [(`(,result)) result])

(define (convert-gvectors item)
  (match item
    [(list-rest x xs) (list* (convert-gvectors x) (convert-gvectors xs))]
    [(? gvector? _) (gvector->vector item)]
    [_ item]))

(define (pad line width end)
  (string-append line (make-string (- width (string-length line)) #\space) end))

(define (evaluate-step todos targets)
  (match-define (cons todo todos-rest) todos)
  (match-define (cons target targets-rest) targets)
  (match todo
    [`#s(evaluate ,env ,eval-item)
     (match eval-item
       [(? number? num) (gvector-add! target num)
                        `#(,todos-rest ,targets)]
       [(? string? str) (gvector-add! target str)
                        `#(,todos-rest ,targets)]
       [(? symbol? name) (define value (stat-env-ref env name))
                         (gvector-add! target value)
                         `#(,todos-rest ,targets)]
       [(list-rest op args)
        (define new-todos `(#s(evaluate ,env ,op)
                            #s(evaluate-args ,env ,args)
                            ,@todos-rest))
        (define new-targets (cons (make-gvector) targets))
        `#(,new-todos ,new-targets)]
       [_ (raise-user-error (format "can't evaluate ~A" eval-item))])]
    [`#s(evaluate-args ,env ,args-item)
     (unless (list? args-item)
       (raise-user-error (format "bad args ~A" args-item)))
     (define op (gvector-ref target 0))
     (cond [(special? op)
            (gvector-set! target 0 (special-item op))
            (for-each #{gvector-add! target %} args-item)
            (define new-todos `(#s(invoke ,env) ,@todos-rest))
            `#(,new-todos ,targets)]
           [(rewriter? op)
            (for-each #{gvector-add! target %} args-item)
            (define new-todos `(#s(invoke ,env) ,@todos-rest))
            `#(,new-todos ,targets)]
           [else
            (define arg-todos (map (lambda (item) `#s(evaluate ,env ,item))
                                   args-item))
            (define new-todos `(,@arg-todos #s(invoke ,env) ,@todos-rest))
            `#(,new-todos ,targets)])]
    [`#s(invoke ,env)
     (evaluate-invoke env target todos-rest targets-rest)]
    [`#s(evaluate-target ,env)
     (define todo-item `#s(evaluate ,env ,(gvector-ref target 0)))
     `#(,(cons todo-item todos-rest) ,targets-rest)]
    [_ (raise-user-error (format "can't evaluate ~A" todo))]))

(define (evaluate-invoke dyn-env form todos targets)
  (match-define (cons sub args) (gvector->list form))
  (match sub
    [`#s(primitive-no-env ,name) (define f (eval name))
                                 (define result (apply f args))
                                 (gvector-add! (first targets) result)
                                 `#(,todos ,targets)]
    [`#s(primitive ,name) (define f (eval name))
                          (define result (apply f dyn-env args))
                          (gvector-add! (first targets) result)
                          `#(,todos ,targets)]
    [`#s(eval-ext ,name) ((eval name) dyn-env args todos targets)]
    [(? subprogram? s) (define stat-env (subprogram-static-parent-env s))
                       (define formals (subprogram-formals s))
                       (unless (= (length formals) (length args))
                         (raise-user-error (format "bad args ~A" args)))
                       (define bindings (map cons formals args))
                       (define new-env (make-env stat-env bindings))
                       (define body (subprogram-body s))
                       (define body-todo `#s(evaluate ,new-env ,body))
                       (define new-todos (list* body-todo todos))
                       `#(,new-todos ,targets)]
    [(? rewriter? r) (define stat-env (rewriter-definition-site-env r))
                     (define formals (rewriter-formals r))
                     (unless (= (length formals) (length args))
                       (raise-user-error (format "bad args ~A" args)))
                     (define bindings (map cons formals args))
                     (define new-env (make-env stat-env bindings))
                     (define body (rewriter-body r))
                     (define body-todo `#s(evaluate ,new-env ,body))
                     (define eval-todo `#s(evaluate-target ,dyn-env))
                     (define new-todos (list* body-todo eval-todo todos))
                     (define new-targets (cons (make-gvector) targets))
                     `#(,new-todos ,new-targets)]
    [_ (raise-user-error (format "can't invoke ~A" sub))]))

(define (evaluate-quote env args todos targets)
  (match args
    [(list arg) (gvector-add! (first targets) arg)]
    [_ (raise-user-error (format "bad quote ~A" args))])
  `#(,todos ,targets))

(define (evaluate-quasiquote env args todos targets)
  `#(,todos ,targets)) ; TODO

(define (evaluate-unquote env args todos targets)
  `#(,todos ,targets)) ; TODO

(define (evaluate-unquote-splicing env args todos targets)
  `#(,todos ,targets)) ; TODO

(define (evaluate-new env args todos targets)
  (match args
    [(list (? symbol? name) value-expr)
     (define todo-value `#s(evaluate ,env ,value-expr))
     (define new-todos (list* todo-value `#s(invoke ,env) todos))
     (define new-target (gvector #s(primitive stat-env-new!) name))
     (define new-targets (cons new-target targets))
     `#(,new-todos ,new-targets)]
    [_ (raise-user-error (format "bad new ~A" args))]))

(define (evaluate-set env args todos targets)
  (match args
    [(list (? symbol? name) value-expr)
     (define todo-value `#s(evaluate ,env ,value-expr))
     (define new-todos (list* todo-value `#s(invoke ,env) todos))
     (define new-target (gvector #s(primitive stat-env-set!) name))
     (define new-targets (cons new-target targets))
     `#(,new-todos ,new-targets)]
    [_ (raise-user-error (format "bad set ~A" args))]))

(define (evaluate-del env args todos targets)
  (match args
    [(list (? symbol? name))
     (stat-env-del! env name)
     `#(,todos ,targets)]
    [_ (raise-user-error (format "bad del ~A" args))]))

(define (evaluate-sub env sub-form todos targets)
  (match sub-form
    [(list-rest (list (? symbol? args) ...) body)
     (unless {(length body) = 1}
       (raise-user-error (format "bad sub body ~A" body)))
     (define sub-value (subprogram env args (first body)))
     (gvector-add! (first targets) sub-value)
     `#(,todos ,targets)]
    [_ (raise-user-error (format "bad sub ~A" sub-form))]))

(define (evaluate-rewrite env rew-form todos targets)
  (match rew-form
    [(list-rest (list (? symbol? args) ...) body)
     (unless {(length body) = 1}
       (raise-user-error (format "bad rewrite body ~A" body)))
     (define rew-value (rewriter env args (first body)))
     (gvector-add! (first targets) rew-value)
     `#(,todos ,targets)]
    [_ (raise-user-error (format "bad rewrite ~A" rew-form))]))

(define (make-primitive p)
  `#s(primitive ,p))

(define (make-primitive-no-env p)
  `#s(primitive-no-env ,p))

(define (make-start-env)
  (make-env 'none
            [list `(!prim . ,(special #s(primitive-no-env make-primitive)))
                  `(!prim-no-env . ,(special #s(primitive-no-env
                                                make-primitive-no-env)))
                  '(quit . #s(primitive-no-env raise-quit))
                  (cons 'quote (special #s(eval-ext evaluate-quote)))
                  (cons 'quasiquote (special #s(eval-ext evaluate-quasiquote)))
                  (cons 'unquote (special #s(eval-ext evaluate-unquote)))
                  (cons 'unquote-splicing
                        (special #s(eval-ext evaluate-unquote-splicing)))
                  `(new . ,(special #s(eval-ext evaluate-new)))
                  `(set . ,(special #s(eval-ext evaluate-set)))
                  `(del . ,(special #s(eval-ext evaluate-del)))
                  `(sub . ,(special #s(eval-ext evaluate-sub)))
                  `(rewrite . ,(special #s(eval-ext evaluate-rewrite)))]))
