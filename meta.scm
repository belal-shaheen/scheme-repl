;; Belal Shaheen
;; metacircular interpreter for a subset of scheme


;; An environment is a list of one element.  That element is an association
;; list.  This allows us to add a binding to an environment.

(define (popl-error . things)
   (display "ERROR: ")
   (for-each display things)
   (newline)
   (*LOOPTOP* 'dontcare))

(define (popl-bind symbol value env)
  (let ((bindings (car env)))
    (set-car! env (cons (list symbol value) bindings)))
  symbol)

(define (popl-get-binding symbol env)
  (if (not (assv symbol (car env))) (popl-error "Undefined variable " (symbol->string symbol))
  (assoc symbol (car env))))

;; return the value of a symbol bound in the given environment
(define (popl-env-value symbol env)
  (let ((pr (popl-get-binding symbol env)))
    (if pr
        (cadr pr)
        (popl-error "Symbol not found"))))

;; popl-define: add a binding to the environment
(define (popl-define symbol value env)
  (popl-bind symbol value env)
  symbol)

;; popl-set!  change the value of a binding in an environment

;; pr = (x 7)
;; (set! x 9)

(define (popl-set! symbol value env)
  (let ((pr (popl-get-binding symbol env)))
    (if pr
        (set-car! (cdr pr) value)
        (popl-error "No binding found for symbol"))))

(define *TOP-ENVIRONMENT*
  (list (list))) ;; totally empty environment

(popl-define '+ + *TOP-ENVIRONMENT*)
(popl-define '- - *TOP-ENVIRONMENT*)
(popl-define '* * *TOP-ENVIRONMENT*)
(popl-define '/ / *TOP-ENVIRONMENT*)
(popl-define '= = *TOP-ENVIRONMENT*)
(popl-define 'cons cons *TOP-ENVIRONMENT*)

;; a function to check duplicates in a list for the lambda function
(define (duplicates? lst)
  (cond ((null? lst) #f)
        ((member (car lst) (cdr lst)) #t)
        (else (duplicates? (cdr lst)))))

(define (popl-eval-lambda expr env)
   ;; expr is something like:  (lambda (a b c) form1 form2)
   (if (< (length (cdr expr)) 2) (popl-error "Error: Empty body")
      (if (duplicates? (cadr expr)) (popl-error 
                                    (string-append 
                                    "Ill-formed special form: (lambda (" 
                                    (symbol->string (car (cadr expr))) 
                                    " "
                                    (symbol->string (cadr (cadr expr))) 
                                    ") " 
                                    (symbol->string (caddr expr))
                                    ")"))
          (list 'popl-lambda
                (second expr)
                (cddr expr)
                env))))



(define (popl-apply function args)
  ;; function--> (popl-lambda VARS body env)
  ;; verify function is a function.\
  (cond ((not (= (length args) (length (cadr function))))
        (popl-error (string-append "Function expected " 
                                  (number->string (length (cadr function))) 
                                  "arguments, but " 
                                  (number->string (length args)) 
                                  " given")))
        (else (let* ((vars (cadr function))
                (body (caddr function))
                (env (cadddr function))
                (newenv (list (car env))) ;; shallow copy.
                (result #!unspecific))
          (for-each
              (lambda (pair) (popl-bind (car pair) (cadr pair) newenv))
                      (zip vars args))  ;; ((x 4) (y 3))
          (for-each
              (lambda (expr) (set! result (popl-eval expr newenv)))
              body)
          result))))

(define (popl-eval-function-call expr env)
  ;; expr--> (function-expr arg1-expr arg2-expr ... argn-expr)
  ;; evaluate all the expressions
  (let ((items (map (lambda (e) (popl-eval e env)) expr)))
    (if (procedure? (car items)) (apply (car items) (cdr items))
                                 (popl-apply (car items) (cdr items)))))

(define (popl-eval-if expr env)
  (let ((condition (popl-eval (cadr expr) env)))
    (if condition
        (popl-eval (caddr expr) env)
        (popl-eval (cadddr expr) env)))) 

(define (popl-eval-set expr env)
  (let* ((symbol (cadr expr)) (value (caddr expr)) (original (popl-env-value symbol env)))
        (popl-set! symbol (popl-eval value env) env)
        original))

(define (popl-eval-let expr env)
  ;; we go over the pairs of vars and bind them then evaluate the bodies based on the new enviroment
  (let ((bindings (cadr expr)) (bodies  (cddr expr)) (newenv (list (car env))) (result #!unspecific))
       (for-each (lambda (pair) (popl-bind (car pair) (popl-eval (cadr pair) env) newenv)) bindings)
       (for-each (lambda (body) (set! result (popl-eval body newenv))) bodies) result))

(define (popl-eval-eq expr env)
  (let ((firstx (cadr expr)) (secondx (caddr expr)))
       (eq? (popl-eval firstx env) (popl-eval secondx env))))

(define (popl-eval-equal expr env)
   (let ((firstx (cadr expr)) (secondx (caddr expr)))
        (equal? (popl-eval firstx env) (popl-eval secondx env))))

(define (popl-eval-let* expr env)
 ;; each time we bind we evaluate the variable so we can bind it depending on the previous one
 (let ((bindings (cadr expr)) (bodies  (cddr expr)) (newenv (list (car env))) (result #!unspecific))
      (for-each (lambda (pair) (popl-bind (car pair) (popl-eval (cadr pair) newenv) newenv)) bindings)
      (for-each (lambda (body) (set! result (popl-eval body newenv))) bodies) result))


(define (popl-eval-cons expr env)
  (let ((x (cadr expr)) (L (caddr expr)))
       (cons (popl-eval x env) (popl-eval L env))))

(define (popl-eval-car expr env)
  (let ((x (cadr expr)))
       (car (popl-eval x env))))

(define (popl-eval-cdr expr env)
  (let ((x (cadr expr)))
       (cdr (popl-eval x env))))

(define (popl-eval-null expr env)
  (let ((firstx (cadr expr)))
       (null? (popl-eval firstx env))))

(define (popl-eval-do expr env)
  (let ((varinits (cadr expr))
        (condition (caddr expr))
        (body (cadddr expr))
        (newenv (list (car env))))
        ;;we loop over the initial vars so we can bind them before we pass them through the recursion
       (for-each (lambda (varinit) (popl-bind (first varinit) (popl-eval (second varinit) newenv) newenv)) varinits)
       (popl-eval-do-helper varinits condition body newenv)))

(define (popl-eval-do-helper varinits condition body env)
  ;; we check the condition, evaluate the body then increament the vars and recurse
  (cond ((popl-eval (car condition) env) (let ((result #!unspecific)) 
          (for-each (lambda (condbody) (set! result condbody)) (cdr condition)) (popl-eval result env)))
          (else (popl-eval body env)
                (for-each (lambda (varinit) (popl-set! (first varinit) (popl-eval (third varinit) env) env)) varinits)
                (popl-eval-do-helper varinits condition body env))))  

(define (popl-eval-list expr env)
  (let ((newenv (list (car env))) (lst (cdr expr)))
        (popl-eval-list-helper lst newenv)))

(define (popl-eval-list-helper lst env)
  (if (null? lst) ()
      (cons (popl-eval (car lst) env) (popl-eval-list-helper (cdr lst) env))))

(define (popl-eval-cond expr env)
  (let ((expressions (cdr expr))
        (fresult #!unspecific)
        (reachend #f))
       (for-each (lambda (expression)
             ;; we go over each condition and evaluate each of it's bodies if its true
             (cond ((and (not (equal? (car expression) 'else)) (popl-eval (car expression) env))
                       (for-each (lambda (body)
                         (set! fresult (popl-eval body env))) (cdr expression))
                         (set! reachend #t))
                   ((and (equal? (car expression) 'else) (equal? reachend #f))
                   (for-each (lambda (body) (set! fresult (popl-eval body env)))
                              (cdr expression))))) expressions) fresult))

(define (popl-eval-help expr env)
  (cond ((number? expr) expr)
        ((symbol? expr) (popl-env-value expr env))
        ((pair? expr)
         (cond ((eq? (first expr) 'define)
                (if (not (= (length expr) 3)) (popl-error (string-append "Ill-formed special form: (define " (symbol->string (cadr expr)) ")"))
                (let ((sym (second expr))
                      (val (popl-eval (third expr) env)))
                  (popl-define sym val env))))
               ((eq? (first expr) 'lambda)
                (popl-eval-lambda expr env))
               ((eq? (first expr) 'let)
                (popl-eval-let expr env))
               ((eq? (first expr) 'let*)
                (popl-eval-let* expr env))
               ((eq? (first expr) 'do)
                (popl-eval-do expr env))
               ((eq? (first expr) 'list)
                (popl-eval-list expr env))
               ((eq? (first expr) 'car)
                (popl-eval-car expr env))
               ((eq? (first expr) 'cdr)
                (popl-eval-cdr expr env))
               ((eq? (first expr) 'set!)
                (popl-eval-set expr env))
               ((eq? (first expr) 'if)
                (popl-eval-if expr env))
               ((eq? (first expr) 'cond)
                (popl-eval-cond expr env))
               ((eq? (first expr) 'eq?)
                (popl-eval-eq expr env))
               ((eq? (first expr) 'equal?)
                (popl-eval-equal expr env))
               ((eq? (first expr) 'quote)
                (second expr))
               ((eq? (first expr) 'null?)
                (popl-eval-null expr env))
              (else (popl-eval-function-call expr env))))
        (else ())))


;; A function for writing things for debugging.
;; Takes an indententation level, a string prefix,
;; and other things.

;; Change this to #f before submitting:
(define *ENABLE-DEBUG* #f)
(define (popl-debug-println level prefix . others)
  (if *ENABLE-DEBUG* (begin
    (do ((i 0 (+ i 1)))
        ((= i level))
      (display " "))
    (display prefix)
    (do ((lst others (cdr lst)))
        ((null? lst))
      (write (car lst)))
    (newline))))

;; This popl-eval is an augmentation that displays what's being
;; evaluated and what's being returned. Hopefully it's helpful
;; for debugging.
(define popl-eval
  (let ((eval-level 0))
    (lambda (expr env)
      (set! eval-level (+ eval-level 1))
      (popl-debug-println eval-level "Evaluating: " expr)
      (let ((result (popl-eval-help expr env)))
        (popl-debug-println eval-level "Returning: " result)
        (set! eval-level (- eval-level 1))
        result))))

;; This popl-repl reimplemented using a do loop body and a helper function

(define (popl-prompt-read)
  (display "H]=> ") (read))

(define *LOOPTOP* #!unspecific)

(define (popl-repl)
  (call-with-current-continuation (lambda (here) (set! *LOOPTOP* here)))
  (do ((expr (popl-prompt-read) (popl-prompt-read)))
      ((equal? expr '(exit)) "Goodbye")
    (write (popl-eval expr *TOP-ENVIRONMENT*))
    (newline)))

;; end
