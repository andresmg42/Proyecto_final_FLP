#lang eopl
(require racket/format)
(require racket/list)

;******************************************************************************************
;Andres David Ortega Arteaga 2241885
;Jose Daniel Trujillo Suarez 2225611

;;;;; Interpretador para lenguaje con condicionales y ligadura local

;; La definición BNF para las expresiones del lenguaje:
;;
;;  <program>       ::= <expression>
;;                      <a-program (exp)>

;;  <expression>    ::= <numero>
;;                      <lit-exp (num)>

;;                  ::= <texto>
;;                      <lit-text (txt)>

;;                  ::= <identifier>
;;                      <var-exp (id)>

;;                  ::= (<expression> <binary-primitive> <expression>)
;;                      primapp-bin-exp(exp1 binary-prim exp2)

;;                  ::= <primitive-unary>(<expression>)
;;                      primapp-un-exp(unary-prim exp)

;;                  ::= Si <expresion> "{" <expresion>  "}" "sino" "{" <expresion> "
;;                      if-exp (test-exp true-exp false-exp)

;;                  ::= declarar ({<identificador> = <expresion> ';' }*)) { <expresion> }

;;                  ::= procedure (<identificador>*(',') ) "{" <expresion> "}"
;;                      procedure-exp (ids cuero)

;;                  ::= "eval" expresion (expresion *(",") )  finalEval
;;                      app-exp

;;                  ::= letrec  {identifier ({identifier}*(,)) = <expression>}* in <expression>
;;                     <letrec-exp proc-names idss bodies bodyletrec>

;; <binary-primitive>  ::= + (primitive-sum)
;;                     ::= ~ (primitive-substract)
;;                     ::= / (primitive-div)
;;                     ::= * (primitive-mult)
;;                     ::= concat (primitive-con)
;;                     ::= > (primitive-greater)
;;                     ::= < (primitive-minor)
;;                     ::= >= (primitive-greater-equal)
;;                     ::= <= (primitive-minor-equal)
;;                     ::= != (primitive-diferent)
;;                     ::= == (primitive-comparator-equal)

;; <unary-primitive>   ::= lenght (primitive-lenght)
;;                     ::= add1 (primitive-add1)
;;                     ::= sub1 (primirtive-sub1)
;;                     ::= neg (primitive-neg-boolean)

;******************************************************************************************

;******************************************************************************************


;Especificación Léxica
(define scanner-spec-simple-interpreter
'((white-sp
   (whitespace) skip)
  (comment
   ("%" (arbno (not #\newline))) skip)
  (identifier
   ("@" letter (arbno (or letter digit "?"))) symbol)
  (entero
   (digit (arbno digit)) number)
  (entero
   ("-" digit (arbno digit)) number)
  (flotante
   (digit (arbno digit) "." digit (arbno digit)) number)
  (flotante
   ("-" digit (arbno digit) "." digit (arbno digit)) number)
  (text
    (letter (arbno (or letter digit "_" ":"))) string)

  ))

;Especificación Sintáctica (gramática)
(define grammar-simple-interpreter
  '(
    ;(globals ("GLOBALS" "{" (arbno identifier "=" expression) "}") globals-exp)
    ;(fusion-lang (globals "," program) fusion-lang-exp)
    ;(program ("PROGRAM" "{" expression "}") a-program)
    (fusion-lang ("GLOBALS" "{" (arbno id-exp "=" expression) "}" "PROGRAM" "{" expression "}") fusion-exp)
    (id-exp ("const" type-exp identifier) const-exp)
    (id-exp ("var" type-exp identifier) identifier-var-exp)
    (id-exp ("proc" type-exp identifier) proc-id-exp)
    (expression (id-exp) var-id-exp)
    (expression ("main""("")" "{" "return" expression "}") main-exp)
    (expression (entero) lit-ent-exp)
    (expression (flotante) lit-float-exp)
    (expression (identifier) var-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)

   ; (expression ("const" type-exp identifier "=" expression ) conts-exp)
    
    (expression (unary-primitive "(" (arbno expression) ")") primapp-un-exp)
    
    (expression
     ( "/" expression primitiva-binaria expression "/")
     primapp-bin-exp)
    
    (expression
     ("\"" text "\"" )
    text-exp)

    (expression
     ("Si" expression "{" expression "}" "sino" "{" expression "}")
     if-exp)

    (expression
     ("let"  (arbno identifier "=" expression) "in" expression)
     localVar-exp)

    (expression
     ("function" "(" (arbno type-exp identifier) ")" "return"
                   expression )
     function-exp)

    ;(expression ("proc" identifier "("(arbno identifier)")" "return" expression) proc-exp)
    
    (expression ( "app""(" expression (arbno expression) ")")
                app-exp)

    (expression
     ("letrec" (arbno  identifier  "=" expression)  "in" expression)  letrec-exp)

    ;(expression ("(" (separated-list expression ",") ")") list-exp)

    ;(expression ("["  (separated-list expression ",") "]") vec-exp)

    ;(expression ("{" (separated-list "\"" text "\"" ":" expression ",") "}") dic-exp)

    (expression ("("type-exp")") empty-list-exp)

    (expression ("[]") empty-vec-exp)
    
    (expression ( "edges" "(" (arbno "(" identifier "," identifier ")" ) ")") edge-exp)

    (expression ( "vertices" "(" (separated-list identifier ",") ")") vertices-exp)

    (expression ( "graph" "(" expression "," expression ")" ";") graph-exp)

     ; características adicionales locals
    (expression ("BLOCK" "{" expression (arbno  expression) "}")
                begin-exp)
    (expression ("set" identifier "=" expression)
                set-exp)
    (expression ("LOCALS" "{" (arbno identifier "=" expression) "}" "{"expression (arbno expression) "}") locals-exp)

    

    
    
    
    ; binary-Primitive-exp
    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("~") primitiva-resta)
    (primitiva-binaria ("/") primitiva-div)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("concat") primitiva-concat)
    (primitiva-binaria (">") primitiva-mayor)
    (primitiva-binaria ("<") primitiva-menor)
    (primitiva-binaria (">=") primitiva-mayor-igual)
    (primitiva-binaria ("<=") primitiva-menor-igual)
    (primitiva-binaria ("!=") primitiva-diferente)
    (primitiva-binaria ("==") primitiva-comparador-igual)

    
    ;unary-primitive-exp
    (unary-primitive ("length") primitive-lenght);operacion unaria para calcula longitud de un string
    (unary-primitive ("add1") primitive-add1);operacion unaria hallar el sucesor de un numero
    (unary-primitive ("sub1") primitive-sub1);operacion unaria hallar el predecesor de un numero
    (unary-primitive ("neg") primitive-neg-boolean);operacion que niega el valor de un booleano
    ;;listas
    (unary-primitive("empty?") primitive-empty)
    (unary-primitive("list?") primitive-list?)
    (unary-primitive("head") primitive-head)
    (unary-primitive("tail")primitive-tail)
    (unary-primitive ("make-list") primitive-make-list)
    (unary-primitive ("append-list") primitive-append-list)
    ;;vectores
    (unary-primitive("vector?") primitive-vector?)
    (unary-primitive ("make-vec") primitive-make-vec)
    (unary-primitive ("make-vec-zise") primitive-make-vec-zise)
    (unary-primitive ("ref-vector") primitive-ref-vector)
    (unary-primitive ("set-vector") primitive-set-vector)
    (unary-primitive ("append-vector") primitive-append-vector)
    (unary-primitive ("delete-val-vector") primitive-delete-vec)
    ;;diccionario
    (unary-primitive ("make-dict") primitive-make-dict)
    (unary-primitive ("dict?") primitive-dict?)
    (unary-primitive ("ref-dict") primitive-ref-dict)
    (unary-primitive ("set-dict") primitive-set-dict)
    (unary-primitive ("append-dict") primitive-append-dict)
    (unary-primitive ("keys-dict") primitive-keys-dict)
    (unary-primitive ("values-dict") primitive-values-dict)
    
    

    ;caracteristicas adicionales
    ;(type-exp ("list" "<" type-exp ">") list-type-exp)
    (unary-primitive ("zero?") zero-test-prim)    
    (type-exp ("int") int-type-exp)
    (type-exp ("float") float-type-exp)
    (type-exp ("String") String-type-exp)
    (type-exp ("bool") bool-type-exp)
    (type-exp ("(" (separated-list type-exp "*") "->" type-exp ")") proc-type-exp)
    ;(type-exp ("list<int>") list-int-type)
    ;(type-exp ("list<float>") list-float-type)
    ;(type-exp ("list<bool>") list-bool-type)
    ;(type-exp ("list<strign>") list-string-type)
    ;(type-exp ("string") string-type-exp)
    (type-exp ("list" "<" type-exp ">") list-type-exp)
    ;(type-exp ("proc") proc-type-exp2)
    ;(type-exp ("const" type-exp) const-type-exp)
    
    
    ))

;Funcion que resuelve las operaciones de cada primitiva binaria 
;apply-binary-primitive: <primitiva> <list-of-expression> -> numero
;apply-primitive: <primitiva> <list-of-expression> -> numero


(define apply-primitive-bin
  (lambda (prim-bin arg1 arg2)
    (let(
        (exp1 (if (pair? arg1) (car arg1) arg1))
        (exp2 (if (pair? arg2) (car arg2) arg2))
        )
    (cases primitiva-binaria prim-bin
      (primitiva-suma () (+ exp1  exp2))
      (primitiva-resta () (- exp1 exp2))
      (primitiva-div () (/ exp1 exp2))
      (primitiva-multi () (* exp1 exp2))
      (primitiva-concat () (string-append exp1 exp2))
      (primitiva-mayor () (valor-verdad? (comparar exp1  exp2 '>)))
      (primitiva-menor () (valor-verdad? (comparar exp1  exp2 '<)))
      (primitiva-mayor-igual () (valor-verdad? (comparar  exp1 exp2 '>=)))
      (primitiva-menor-igual () (valor-verdad? (comparar  exp1 exp2 '<=)))
      (primitiva-diferente () (valor-verdad? (not (eqv? exp1 exp2))))
      (primitiva-comparador-igual () (valor-verdad? (equal? exp1 exp2)))
      (else "faltan casos bianrio")
 
      
      
                       
      ))))

;Funcion que resuelve las operaciones de cada primitiva unaria
;apply-unary-primitive: <primitiva> <list-of-expression> -> numero
(define apply-unary-primitive
  (lambda (prim arg)
    (cases unary-primitive prim
      (primitive-lenght () (string-length (car arg)))
      (primitive-add1 () (+ 1 (car arg)))
      (primitive-sub1 () (- (car arg) 1))
      (primitive-neg-boolean () (if (eqv? (car arg) "true") "false"
                                    "true"))
      ;listas
      (primitive-empty () (valor-verdad? (equal? (car arg) "[]")))
      (primitive-head () (caaar arg))
      (primitive-tail () (cdr (caar arg)))
      (primitive-append-list () (append (car arg) (cadr arg)))
      (primitive-make-list () (if (null? (car arg)) '() arg))
      (primitive-list? () (pair? (caar arg)))
      ;vectores
      (primitive-vector? () (valor-verdad? (vector? (car arg))))
      (primitive-make-vec () (list->vector arg))
      (primitive-make-vec-zise () (make-vec-zise arg))
      (primitive-ref-vector () (vector-ref (car arg) (cadr arg)))
      (primitive-set-vector () (vector-set! (car arg) (cadr arg) (caddr arg)))
      (primitive-append-vector () (append (vector->list (car arg)) (cadr arg)))
      (primitive-delete-vec () (list->vector (eliminar-pos (vector->list (car arg)) (cadr arg) 0)))
      ;diccionarios
      (primitive-make-dict () (list (car arg) (list->vector (cadr arg))))
      (primitive-dict? () (valor-verdad? (dict? (car arg))))
      (primitive-ref-dict () (dict-values (car arg) (cadr arg)))
      (primitive-set-dict () (set-dict (car arg) (cadr arg) (caddr arg)))
      (primitive-append-dict () ( append-dict (car arg) (cadr arg) (caddr arg)))
      (primitive-keys-dict () (caar arg))
      (primitive-values-dict () (vector->list (cadr (car arg))))
      (else "faltan casos unario")
      )))



;---------------------------------------------------------------------TIPOS----------------------------------------------------

;El Interpretador + checker (FrontEnd + Evaluación + señal para lectura )

(define interpretador-tipos
  (sllgen:make-rep-loop  "--> "
    (lambda (pgm) (aux-interpretador  pgm)) 
    (sllgen:make-stream-parser 
      scanner-spec-simple-interpreter
      grammar-simple-interpreter)))

(define aux-interpretador
  (lambda (x)
    (if (type? (type-of-program x)) (eval-program  x) 'error-iterpretador)))

;***********************************************************************************************************************
;*********************************************   Definición tipos     **************************************************
;***********************************************************************************************************************

(define-datatype type type?
  (atomic-type
   (name symbol?))
  (proc-type
   (arg-types (list-of type?))
   (result-type type?)))

;***********************************************************************************************************************
;***********************************************************************************************************************

;***********************************************************************************************************************
;*************************************************   Type Checker     **************************************************
;***********************************************************************************************************************

;type-of-program: <programa> -> type
; función que chequea el tipo de un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)
(define type-of-program
  (lambda (fusion)
    (cases fusion-lang fusion
      (fusion-exp (id-exp g-exps p-exp) (type-of-fusion-lang id-exp g-exps p-exp (empty-tenv))))))



(define extend-tenv-recursively
   (lambda (id-exps exps tenv)
     (let*(
           (len (length id-exps))
           (vec (make-vector len))
           (names (make-vector len))
           ;(reult-types (expand-type-expressions result-texps))
           ;(tenv-for-body (extend-tenv names vec tenv))
           
           )
       
       (for-each
        (lambda (pos body id)
          
          (let*(
              (list-name-texp (cases id-exp id (const-exp (texp name) (list name texp)) (identifier-var-exp (texp name) (list name texp)) (proc-id-exp (texp name) (list name texp))))
              
              
              
              (result-type (expand-type-expression (cadr list-name-texp)))
               
               )
          (if (proc? body)
              
              (cases proc body (procedure (texps ids body)
              (let(

                   (arg-types (expand-type-expressions texps))
                   
                   )
                (vector-set! vec pos (proc-type arg-types result-type)))))

              (vector-set! vec pos result-type)
                  
              )
            (vector-set! names  pos (car list-name-texp))
            
            ))
       (iota len) exps id-exps)

       
       (extend-tenv (vector->list names) (vector->list vec) tenv)


       )))

#|(define type-of-fusion-lang
        (lambda (ids exps p-body tenv)
          (letrec(
              
              (list-id-exp (lambda (ids list-texps list-names)
                             (if(null? ids) (list list-texps list-names)
                                (let(
                                     (l-exp (cases id-exp (car ids) (const-exp (texp id) (list texp id)) (identifier-var-exp (texp id) (list texp id)) (proc-id-exp (texp id) (list texp id))))
                                     
                                     )
                                  (list-id-exp (cdr ids) (cons (car l-exp) list-texps) (cons (cadr l-exp) list-names))
                                  ))))
              (list-names-ids (list-id-exp ids (list) (list)))
                                 
              (names (cadr list-names-ids))
              
              (result-types (expand-type-expressions (car list-names-ids)))
              
              (env (extend-tenv-recursively result-types names exps tenv))
              
              )
         (for-each
        (lambda (id body result-type)
          (if (proc? body)
              (cases proc body (procedure (texps ids body)
                                          (let(
                                               (proc-id? (cases id-exp id (const-exp (texp id) #f) (identifier-var-exp (texp id) #f) (proc-id-exp (texp id) #t)))
                                               (arg-types (expand-type-expressions texps))

                                               )
                                            (if (not proc-id?) (eopl:error 'fusion-lang "id-exp was not proc")
                                                
                                            (check-equal-type!
                                            (type-of-expression
                                             body
                                            (extend-tenv ids arg-types env))
                                            result-type body))

                                            )))
                                                                                 
              
              
              (check-equal-type!
               (type-of-expression body env) result-type body)

        
              
              )) ids exps result-types)

          (type-of-expression p-body env))))
               |#
(define type-of-fusion-lang
  (lambda(id-exps exps p-body tenv)
 (let(
         #|(list-id-exp (lambda (ids list-texps list-names)
                             (if(null? ids) (list list-texps list-names)
                                (let(
                                     (l-exp (cases id-exp (car ids) (const-exp (texp id) (list texp id)) (identifier-var-exp (texp id) (list texp id)) (proc-id-exp (texp id) (list texp id))))
                                     
                                     )
                                  (list-id-exp (cdr ids) (cons (car l-exp) list-texps) (cons (cadr l-exp) list-names))
                                  ))))
              (l (list-id-exp ids (list) (list)))
         
              (result-types (expand-type-expressions (reverse (car l))));AQUI ESTA EL PROBLEMA!
              (names (cadr l))|#
                            
              (env (extend-tenv-recursively id-exps exps tenv))
              
              )
   
         (for-each
        (lambda (body id)
          (let*(
               (texp (cases id-exp id (const-exp (texp name) texp) (identifier-var-exp (texp name) texp) (proc-id-exp (texp name) texp)))
               ;(proc-id-exp? (cases id-exp id (proc-id-exp (texp name) #t) (else #f)))
               ;(const-id-exp? (cases id-exp id (const-id-exp (texp name) #t) (else #f)))
               ;(var-id-exp? (cases id-exp id (var-id-exp (texp name) #t) (else #f)))
               (result-type (expand-type-expression texp))
               
               )
            
              (if (proc? body) 
              
              (cases proc body (procedure (texps ids body)
                                          (let
                                               (
                                               (arg-types (expand-type-expressions texps))

                                               )
                                            (check-equal-type!
                                            (type-of-expression
                                             body
                                            (extend-tenv ids arg-types env))
                                            result-type body))))
              
              
            (check-equal-type!
               (type-of-expression body env) result-type body)

              ))) exps id-exps)

          (type-of-expression p-body env)
   )))

          
          
                                                 

                                          
          
          
       
       
    

;eval-expression: <expression> <enviroment> -> type
; chequea el tipo de la expresión en el ambiente de entrada
(define type-of-expression
  (lambda (exp tenv)
    (cases expression exp
      (lit-ent-exp (number)
               int-type)
      (text-exp (text) string-type)
  
      (lit-float-exp (number)
                     float-type)
     
      (true-exp ()
                bool-type)
      (false-exp ()
                 bool-type)
      (var-exp (id)
               (apply-tenv tenv id))
      (empty-list-exp (t) (expand-type-expression t))
       
      (if-exp (test-exp true-exp false-exp)
              (let ((test-type (type-of-expression test-exp tenv))
                    (false-type (type-of-expression false-exp tenv))
                    (true-type (type-of-expression true-exp tenv)))
                (check-equal-type! test-type bool-type test-exp)
                (check-equal-type! true-type false-type exp)
                true-type))
      (function-exp (texps ids body)
                (type-of-proc-exp texps ids body tenv))
      (primapp-un-exp (prim rands)
                   (type-of-application
                    (type-of-primitive prim rands tenv)
                    (types-of-expressions rands tenv)
                    prim rands exp))
      
      (primapp-bin-exp(exp1 prim exp2)
                      (type-of-application
                       (type-of-primitive-bin prim exp1 exp2 tenv)
                       (types-of-expressions (list exp1 exp2) tenv)
                       prim (list exp1 exp2) exp))
                       
                      
      (app-exp (rator rands)
               (type-of-application
                (type-of-expression rator tenv)
                (types-of-expressions rands tenv)
                rator rands exp))

      (set-exp (id exp)
               (let(
                    (id-type (apply-tenv tenv id))
                    (exp-type (type-of-expression exp tenv))
                    )
                 (check-equal-type! id-type exp-type exp)
                 id-type
                 
                 ))
                     
      #|(let-exp (ids rands body)
               (type-of-let-exp ids rands body tenv))|#
      #|(letrec-exp (result-texps proc-names texpss idss bodies letrec-body)
                  (type-of-letrec-exp result-texps proc-names texpss idss bodies
                                      letrec-body tenv)))))|#
      (else 'faltancasos)
      )))

;check-equal-type!: <type> <type> <expression> -> 
; verifica si dos tipos son iguales, muestra un mensaje de error en caso de que no lo sean
(define check-equal-type!
  (lambda (t1 t2 exp)
    (if (not (equal? t1 t2))
        (eopl:error 'check-equal-type!
                    "Types didn’t match: ~s != ~s in~%~s"
                    (type-to-external-form t1)
                    (type-to-external-form t2)
                    exp)
        #t)))

;type-to-external-form: <type> -> lista o simbolo
; recibe un tipo y devuelve una representación del tipo facil de leer
(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (atomic-type (name) name)
      (proc-type (arg-types result-type)
                 (append
                  (arg-types-to-external-form arg-types)
                  '(->)
                  (list (type-to-external-form result-type)))))))

(define arg-types-to-external-form
  (lambda (types)
    (if (null? types)
        '()
        (if (null? (cdr types))
            (list (type-to-external-form (car types)))
            (cons
             (type-to-external-form (car types))
             (cons '*
                   (arg-types-to-external-form (cdr types))))))))

;type-of-proc-exp: (list-of <type-exp>) (list-of <symbol>) <expression> <tenv> -> <type>
; función auxiliar para determinar el tipo de una expresión de creación de procedimiento
(define type-of-proc-exp
  (lambda (texps ids body tenv)
    (let ((arg-types (expand-type-expressions texps)))
      (let ((result-type
             (type-of-expression body
                                 (extend-tenv ids arg-types tenv))))
        (proc-type arg-types result-type)))))

;type-of-application: <type> (list-of <type>) <symbol> (list-of <symbol>) <expresion> -> <type>
; función auxiliar para determinar el tipo de una expresión de aplicación
(define type-of-application
  (lambda (rator-type rand-types rator rands exp)
    (cases type rator-type
      (proc-type (arg-types result-type)
                 (if (= (length arg-types) (length rand-types))
                     (begin
                       (for-each
                        check-equal-type!
                        rand-types arg-types rands)
                       result-type)
                     (eopl:error 'type-of-expression
                                 (string-append
                                  "Wrong number of arguments in expression ~s:"
                                  "~%expected ~s~%got ~s")
                                 exp
                                 (map type-to-external-form arg-types)
                                 (map type-to-external-form rand-types))))
      (else
       (eopl:error 'type-of-expression
                   "Rator not a proc type:~%~s~%had rator type ~s"
                   rator (type-to-external-form rator-type))))))

;type-of-primitive: <primitive> -> <type>
; función auxiliar para determinar el tipo de una primitiva
(define type-of-primitive
  (lambda (prim rands tenv)
     (let*(
        (arg-types (types-of-expressions rands tenv))
        (type  (if (not (null? arg-types)) (car arg-types) (eopl:error 'type-of-primitive "types not found"))) 
        (equal-types? (or ((list-of (lambda(type) (equal? type (car arg-types)))) arg-types) (equal? type list-empty-type)))
        (validate-type?  (or (equal? type float-type) (equal? type int-type) (equal? type bool-type) (equal? type string-type) (equal? type list-empty-type))) 
        ;(len (length arg-types))
        ;(make-list-types (lambda (type len) (if (equal? len 0) '() (cons type (make-list-types type (- len 1))))))
        
        
        )
    (cases unary-primitive prim
      (primitive-lenght () (proc-type (list string-type) int-type))
      ;(primitive-add1 () (proc-type (list int-type) int-type))
      ;(primitive-sub1 () (proc-type (list int-type) int-type))
      (primitive-neg-boolean () (proc-type (list bool-type) bool-type))
      ;listas
      
      ;(primitive-list? () (proc-type (list list-type) bool-type))
      ;(primitive-head () (proc-type (list list-type) (let( (head-type (type-of-expression (car rands))) head-type))))
      
      
      (primitive-add1 ()
                 (proc-type (list int-type) int-type))
      (primitive-sub1 ()
                 (proc-type (list int-type) int-type))
      
      (zero-test-prim ()
                      (proc-type (list int-type) bool-type))
      
      ;listas
      (primitive-list? () (proc-type (list type) bool-type))

      (primitive-head ()  (proc-type (list type) (get-type-list type)))
      
      (primitive-tail () (proc-type (list type) type))
      
      (primitive-make-list () (proc-type (if (and equal-types? validate-type?) arg-types (eopl:error 'type-of-primitive "the list types weren't equals or weren't correct type")) (list-type type)))

      (primitive-empty () (proc-type (list list-empty-type) bool-type))

      ;(primitive-append-list () (proc-type (
      

      

      
      
      (else 'faltan_casos)

      ))))

 ;funcion que saca el tipo de los elementos de un tipo lista
(define get-type-list
  (lambda (t)
    (let(
         (s (cases type t (atomic-type (sym) sym) (else (eopl:error 'get-type-list "given: proc type ,expected: list type"))))
         )
      (cond
        [(equal? s 'list<int>) int-type]
        [(equal? s 'list<float>) float-type]
        [(equal? s 'list<bool>) bool-type]
        [(equal? s 'list<string>) string-type]
        [else (eopl:error 'get-type-list: "type not supported: ~s" s)]))))
        
  

(define type-of-primitive-bin
  (lambda (prim exp1 exp2 tenv)
    (let(
         (exp1-type  (type-of-expression exp1 tenv))
          (exp2-type (type-of-expression exp2 tenv))
          (chequeo-int-float (lambda(exp1-type exp2-type)
                             (if (and (or (equal? exp1-type int-type) (equal? exp1-type float-type)) (check-equal-type!  exp1-type exp2-type prim))
                                 (proc-type (list exp1-type exp2-type ) exp1-type)
                                 
                             (eopl:error 'primitive-bin
                    "Types didn't supported. given: ~s,~s. expected: int or float"
                    (type-to-external-form exp1-type)
                    (type-to-external-form exp2-type)))
                             ))
          (chequeo-mayor-menor (lambda (t1 t2)
                                (if (and (or (equal? t1 int-type) (equal? t1 float-type) (equal? t1 string-type)) (check-equal-type!  t1 t2 prim))
                                    (proc-type (list t1 t2) bool-type)
                                    (eopl:error 'primitive-bin "types didn't support"))))
          (chequeo-concat (lambda (t1 t2)
                                 (if (and (equal? t1 string-type) (check-equal-type! t1 t2)) (proc-type (list string-type string-type) string-type)
                                     (eopl:error 'primitive-bin
                    "Types didn't supported. given: ~s,~s. expected: string string"
                    (type-to-external-form t1)
                    (type-to-external-form t2)))))
                                     
           
           )

     (cases primitiva-binaria prim

      (primitiva-suma () (chequeo-int-float exp1-type exp2-type )) 
      (primitiva-resta () (chequeo-int-float exp1-type exp2-type ))
      (primitiva-div () (chequeo-int-float exp1-type exp2-type ))
      (primitiva-multi () (chequeo-int-float exp1-type exp2-type ))
      (primitiva-comparador-igual () (proc-type (list exp1-type exp2-type) bool-type))
      (primitiva-diferente () (proc-type (list exp1-type exp2-type) bool-type))
      (primitiva-mayor () (chequeo-mayor-menor exp1-type exp2-type))
       (primitiva-menor () (chequeo-mayor-menor exp1-type exp2-type))
       (primitiva-mayor-igual () (chequeo-mayor-menor exp1-type exp2-type))
       (primitiva-menor-igual () (chequeo-mayor-menor exp1-type exp2-type))
       (primitiva-concat () (chequeo-concat exp1-type exp2-type))
       
      (else 'faltan_casos)))))

;types-of-expressions: (list-of <type-exp>) <tenv> -> (list-of <type>)
; función que mapea la función type-of-expresion a una lista
(define types-of-expressions
  (lambda (rands tenv)
    (map (lambda (exp) (type-of-expression exp tenv)) rands)))

;type-of-primitive: (list-of <symbol>) (list-of <expression>) <expression> <tenv> -> <type>
; función auxiliar para determinar el tipo de una expresión let
(define type-of-let-exp
  (lambda (ids rands body tenv)
    (let ((tenv-for-body
           (extend-tenv
            ids
            (types-of-expressions rands tenv)
            tenv)))
      (type-of-expression body tenv-for-body))))

;type-of-primitive: (list-of <type-exp>) (list-of <symbol>) (list-of (list-of <type-exp>)) (list-of (list-of <symbol>)) (list-of <expression>) <expression> <tenv> -> <type>
; función auxiliar para determinar el tipo de una expresión letrec
(define type-of-letrec-exp
  (lambda (result-texps proc-names texpss idss bodies letrec-body tenv)
    (let ((arg-typess (map (lambda (texps)
                             (expand-type-expressions texps))
                           texpss))
          (result-types (expand-type-expressions result-texps)))
      (let ((the-proc-types
             (map proc-type arg-typess result-types)))
        (let ((tenv-for-body
               (extend-tenv proc-names the-proc-types tenv)))
          (for-each
           (lambda (ids arg-types body result-type)
             (check-equal-type!
              (type-of-expression
               body
               (extend-tenv ids arg-types tenv-for-body))
              result-type
              body))
           idss arg-typess bodies result-types)
          (type-of-expression letrec-body tenv-for-body))))))

;***********************************************************************************************************************
;***********************************************************************************************************************

;***********************************************************************************************************************
;********************************************  Ambientes de tipos  *****************************************************
;***********************************************************************************************************************

(define-datatype type-environment type-environment?
  (empty-tenv-record)
  (extended-tenv-record
    (syms (list-of symbol?))
    (vals (list-of type?))
    (tenv type-environment?)))

(define empty-tenv empty-tenv-record)
(define extend-tenv extended-tenv-record)

(define apply-tenv 
  (lambda (tenv sym)
    (cases type-environment tenv
      (empty-tenv-record ()
        (eopl:error 'apply-tenv "Unbound variable ~s" sym))
      (extended-tenv-record (syms vals env)
        (let ((pos (list-find-position sym syms)))
          (if (number? pos)
            (list-ref vals pos)
            (apply-tenv env sym)))))))

;***********************************************************************************************************************
;***********************************************************************************************************************

;***********************************************************************************************************************
;****************************************************  Tipos  **********************************************************
;***********************************************************************************************************************

(define int-type
  (atomic-type 'int))

(define bool-type
  (atomic-type 'bool))

(define float-type
  (atomic-type 'float))

(define string-type
  (atomic-type 'string))

(define list-empty-type
  (atomic-type 'empty))





(define list-type
  (lambda (typ) (atomic-type (string->symbol (string-append "list<" (symbol->string (cases type typ (atomic-type (t) t) (else (eopl:error 'list-type "no atomic type"))))  ">"  )))))



(define expand-type-expression
  (lambda (texp)
    (cases type-exp texp
      (int-type-exp () int-type)
      (bool-type-exp () bool-type)
      (float-type-exp () float-type)
      (String-type-exp () string-type)
      (list-type-exp (ty-e) (list-type (expand-type-expression ty-e)))
      ;(list-type-exp (type-exp) list-type)
      ;(list-int-type () (list-type int-type))
      ;(list-float-type () (list-type float-type))
      ;(list-bool-type () (list-type bool-type))
      ;(list-string-type () (list-type string-type))
      (proc-type-exp (arg-texps result-texp)
                     (proc-type
                      (expand-type-expressions arg-texps)
                      (expand-type-expression result-texp)))
      
      (else 'faltancasos)
      )))

(define expand-type-expressions
  (lambda (texps)
    (map expand-type-expression texps)))



;***********************************************************************************************************************
;***********************************************************************************************************************



;---------------------------------------------------------------------TIPOS----------------------------------------------------
                  
  

;Funcione que retorna "true" si una operacion binaria es verdadera, o "false" si
;la exprecion es falsa
;valor_verdad?: boolean => string
;usage:(valor-verdad? boolean) => "true" si el booleano es #t o "false" de lo contrario


(define valor-verdad?
  (lambda (bool)
   bool))


;Tipos de datos para la sintaxis abstracta de la gramática
;Construidos automáticamente:

(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)))

;-----------------------------------------------------------------------------------------------
;Parser, Scanner, Interfaz

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados)
(define scan&parse
  (sllgen:make-string-parser scanner-spec-simple-interpreter grammar-simple-interpreter))


;El Analizador Léxico (Scanner)
(define just-scan
  (sllgen:make-string-scanner scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Interpretador (FrontEnd + Evaluación + señal para lectura )
(define interpretador
  (sllgen:make-rep-loop  "--> "
    (lambda (pgm) (eval-program  pgm)) 
    (sllgen:make-stream-parser 
      scanner-spec-simple-interpreter
      grammar-simple-interpreter)))

;-----------------------------------------------------------------------------------------------
;El Interprete


(define eval-program
  (lambda (flang)
    (cases fusion-lang flang
      (fusion-exp (id-exps exps program-body)
                       (let(
                            #|(list-id-exp (map (lambda (id-e) (cases id-exp id-e (cons-exp (texp identifier) (list  identifier 'const))
                                             (identifier-exp (texps identifier) (list identifier 'no-const)))) id-exps))|#
                            (env 
                                   (let(
                                        (bodies (eval-rands exps (empty-env)))
                                        )
                                     (extend-env-recursively2 id-exps bodies (empty-env))))
                            
                            )
                         (eval-expression program-body env)
                         )
                       ))))


                                                                 

;ambiente inicial
#|(define init-env
  (lambda ()
    (extend-env
     '(@a @b @c @d @e @f)
     '(1 2 3 "hola" "FLP" (non-empty-pair 'a 'b) )
     (empty-env))))|#


; funciones auxiliares para aplicar eval-expression a cada elemento de una 
; lista de operandos (expresiones)
(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

;funcion que aplica eval-expression a un solo elemento
(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))


        
;Funcion que extiende un ambiente y evalua un procedimiento en ese nuevo ambiente extendido
;apply-procedure: <procedure> <list-of expression> -> numero
(define apply-procedure
  (lambda (proc args)
    (cases procval proc
      (closure (ids body env)
              (if ((list-of pair?) args) 
             (eval-expression body (extend-env ids (map (lambda (arg) (car arg)) args) (map (lambda (arg) (cadr arg)) args) env))
             (eval-expression body (extend-env ids args (make-boolean-list (length args) #f) env))
               )))))
               
               




;-------------------------------------------------------------------------------------------
;Procedimientos
;define-datatype de los procedimientos
(define-datatype procval procval?
  (closure
   (ids (list-of symbol?))
   (body expression?)
   (env environment?)))

;-------------------------------------------------------------------------------------------
;Ambientes
;definición del tipo de dato ambiente
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vec vector?)
   (const (list-of boolean?))
   (env environment?)))

(define scheme-value? (lambda (v) #t))

;empty-env:      -> enviroment
;función que crea un ambiente vacío
(define empty-env  
  (lambda ()
    (empty-env-record)))       ;llamado al constructor de ambiente vacío 


;extend-env: <list-of symbols> <list-of numbers> enviroment -> enviroment
;función que crea un ambiente extendido
(define extend-env
  (lambda (syms vals consts env)
    (extended-env-record syms (list->vector vals) consts env)))



(define extend-env-recursively2
  (lambda (id-exps bodies old-env)
    (let* (
      (len (length id-exps))
      (vec (make-vector len))
      (names (map (lambda (id) (cases id-exp id (const-exp (texp name) name) (identifier-var-exp (texp name) name) (proc-id-exp (texp name) name))) id-exps))
      (consts (map (lambda (id) (cases id-exp id (const-exp (texp name) #t) (else #f))) id-exps))
      (env (extended-env-record names vec consts old-env ))
      )
      
      (for-each
            (lambda (pos body)
              (if (proc? body)
                  (let(
                       (ids-body (cases proc body (procedure (texps ids body) (list ids body)))) 

                       )
              (vector-set! vec pos (closure (car ids-body) (cadr ids-body) env))
                    )
              (vector-set! vec pos  body)
              ))
                  
            (iota len) bodies)
           env)))

;iota: number -> list
;función que retorna una lista de los números desde 0 hasta end
(define iota
  (lambda (end)
    (let loop ((next 0))
      (if (>= next end) '()
        (cons next (loop (+ 1 next)))))))



;función que busca un símbolo en un ambiente
(define apply-env
  (lambda (env sym)
    (let(
         (val (apply-env-ref env sym))
         )
         
         (if (reference? (car val)) (list (deref (car val)) (cadr val))
             val))))
     ;(apply-env-ref env sym)))
    ;env))
(define apply-env-ref
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
                        (eopl:error 'apply-env-ref "No binding for ~s" sym))
      (extended-env-record (syms vals consts env)
                           (let* (
                                 
                                 (pos (rib-find-position sym syms))
                                 
                                 
                                 
                                 )
                             (if (number? pos)
                                 (let(
                                      (const (list-ref consts pos))
                                      )
                                 (if const (list (vector-ref vals pos) const)
                                 (list (a-ref pos vals) const)
                                 ))
                                 (apply-env-ref env sym)))))))



;*******************************************************************************************
;Referencias

(define-datatype reference reference?
  (a-ref (position integer?)
         (vec vector?)))

(define deref
  (lambda (ref)
    (primitive-deref ref)))

(define primitive-deref
  (lambda (ref)
    (cases reference ref
      (a-ref (pos vec)
             (vector-ref vec pos)))))

(define setref!
  (lambda (ref val)
    (primitive-setref! ref val)))

(define primitive-setref!
  (lambda (ref val)
    (cases reference ref
      (a-ref (pos vec)
             (vector-set! vec pos val)))))


;****************************************************************************************
;Funciones Auxiliares-referencias

; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de un ambiente

(define rib-find-position 
  (lambda (sym los)
    (list-find-position sym los)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (equal? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

;******************************************************************************************


;-------------------------------------------------------------------------------------------
;Funciones Auxiliares

; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de un ambiente


(define list-find-position-string
  (lambda (str los)
    (list-index (lambda (str1) (equal? str1 str)) los)))



;funcion que compara 2 strings.
;comparar-strings?: string x string x symbol => boolean
;usage:(comparar-string string1 string2 comparador) => retorna un booleano, resultado de comparar los strings1 y string2 con un determinado comparador que ingresa como simbolo

(define comparar-strings?
  (lambda (string1 string2 comparador)
    (cond
        [(equal? comparador '<) (string<? string1 string2)]
        [(equal? comparador '>) (string>? string1 string2)]
        [(equal? comparador '>=) (string>=? string1 string2)]
        [(equal? comparador '<=) (string<=? string1 string2)]
        [else (eopl:error "no se pueden comparar los strings")])))

;funcion que compara dos numeros con un determinado comparador en forma de simbolo que resive como parametro.        
(define comparar-numeros?
  (lambda (num1 num2 comparador)
    (cond
        [(equal? comparador '<) (< num1 num2)]
        [(equal? comparador '>) (> num1 num2)]
        [(equal? comparador '>=) (>= num1 num2)]
        [(equal? comparador '<=) (<= num1 num2)]
        [else (eopl:error "no se pueden comparar los numeros")])))        
    

;funcion que utiliza las funciones comprar-numeros? y comparar-strings? para comparar numeros y strings. retorna un booleano.
(define comparar
  (lambda (e1 e2 comparador)
    (cond
      [(and (string? e1) (string? e2)) (comparar-strings? e1 e2 comparador)]
      [(and (number? e1) (number? e2)) (comparar-numeros? e1 e2 comparador)]
      [else (eopl:error "valor esperado, dos strings o dos flotantes")])))


        
         





;funcion que crea un vector de un tamaño determinado y lo llena con un parametro determinado.
(define make-vec-zise
   (lambda (arg)
     (letrec(
           (tamaño (if (null? arg) 0 (car arg)))
          (relleno (if (null? arg) '() (cadr arg)))
          
          (crear
           (lambda(tamaño relleno)
             (if (equal? tamaño 0) '()
                 (cons relleno (crear (- tamaño 1) relleno))
                 )))
          )
          (list->vector (crear tamaño relleno))
       )))





;funcion que elimina un elemento de una lista en determinada posicion. 
(define eliminar-pos
   (lambda (arg pos acc)
     (if (null? arg) '()
         (cond
           [(not (equal? acc pos)) (cons (car arg) (eliminar-pos (cdr arg) pos (+ acc 1)))]
           [(and (equal? acc pos) (not (null? (cdr arg)))) (cons (cadr arg) (eliminar-pos (cddr arg) pos (+ acc 2)))]
           [else '()]
           ))))



;funcion que comprueba si la lista que se le pasa como parametro es la representacion interna de un diccionario.
 (define dict?
  (lambda (arg)
    (let(
        (keys (car arg))
        (values (cadr arg))
      )
    (cond
      [(not (pair? keys)) #f]
      [(not (vector? values)) #f]
      [(not ((list-of string?) keys)) #f]
      [(not (comprovar-verdad values)) #f]
      [else #t]))))
      
(define comprovar-verdad
  (lambda (vec)
    (letrec(
         (v (vector->list vec))
         (t (map (lambda (x) (or (number? x) (boolean? x) (string? x) (symbol? x))) v ))
         (valor-v (lambda (l) (if (null? l) #t (and (car l) (valor-v  (cdr l))))))
         )
      (valor-v t)
      )))

;funcion que resive una representacion interna de un diccionario y una clave. la funcion retorna el valor del diccionario asociado a dicha clave.
(define dict-values
  (lambda (dict key)
    (let(
    (pos (list-find-position-string key (car dict)))
    
    )
    (if (not (boolean? pos)) (vector-ref (cadr dict)  pos) "no encontrado"))))

;funcion que modifica un valor asociado a una clave en un diccionario. retorna el diccionario modificado
(define set-dict
  (lambda (dict key value)
    (let*(
         (pos (list-find-position-string key (car dict)))
         (v (vector-set! (cadr dict) pos value))
         )
      dict
      )))

;funcion que agrega nuevos elementos clave valor a un diccionario. retorna un diccionario con los nuevos elementos agregados

(define append-dict
  (lambda (dict keys values)
    (if (and (dict? dict) (equal? (length keys) (length values)))
    (let* (
          (new-keys (append (car dict) keys))
          (new-values (append (vector->list (cadr dict)) values))
          (new-values-v (list->vector new-values))
          (d (list new-keys new-values-v))
          )
      (if (dict? d ) d "la lista de claves o valores es de tipo incorrecto")
      )
    "los parametros no son los adecuados"
    )))




;eval-expression: <expression> <enviroment> -> numero
; evalua la expresión en el ambiente de entrada

(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (lit-ent-exp (datum) datum)
      (lit-float-exp (datum) datum)
      (var-exp (id) (apply-env env id))
      (text-exp (text) text)
      (true-exp () #t)
      (false-exp () #f)
      (empty-list-exp (t) '())
      (empty-vec-exp () (vector))
      (primapp-un-exp (prim rand)
                  (let ((arg (eval-rands rand env)))
                   (apply-unary-primitive prim arg)))
      
      (primapp-bin-exp (exp1 prim exp2)
                  (let ((arg1 (eval-expression exp1 env))
                        (arg2 (eval-expression exp2 env)))
                    (apply-primitive-bin prim  arg1 arg2)))

      (if-exp(test-exp true-exp false-exp)
              (if(valor-verdad? (eval-expression test-exp env))
                (eval-expression true-exp env)
                (eval-expression false-exp env)))

      (localVar-exp(ids exps body)
                   #|(let ((args (eval-rands exps env)))
                   (eval-expression body
                                    (extend-env ids args env)))|# 1)

      (function-exp (texps ids body) (procedure texps ids body))
      
      ;(proc-exp (name ids body) (procedure ids body))

      (app-exp (rator rands)
                 (let (
                     (proc (car (eval-expression rator env)))
                     (args (eval-rands rands env))
                     
                     )
                     (if (procval? proc)
                         (apply-procedure proc args)
                         (eopl:error 'eval-expression
                                 "Attempt to apply non-procedure ~s" proc)
                         )
                 )
               )
      
      #|(app-exp (rator rands)
               (args (eval-rands rands env))|#
      
      
      #|(letrec-exp (names  exps letrec-body)
                   (let (
                         (args (eval-rands exps env))
                   )(eval-expression letrec-body (extend-env-recursively2 names args env)
                     )))|#
      
;-------------------------------------------------------------------------
      
      ;(list-exp (args)
      ;          (eval-rands args env))
      ;(vec-exp (args) (list->vector (eval-rands args env)))

      ;(dic-exp (keys values) (list keys (list->vector (eval-rands values env))))

      ;set
       (set-exp (id rhs-exp)
                (let(
                     (val (car (apply-env-ref env id)))
                     )
               (begin
                 (if (reference? val)
                 (setref!
                  val
                  (eval-expression rhs-exp env))
                 (eopl:error 'set-exp "inmutable value ~s" val))
                 1)))

      ;block
      (begin-exp (exp exps) 
                 (let loop ((acc (eval-expression exp env))
                             (exps exps))
                    (if (null? exps) 
                        acc
                        (loop (eval-expression (car exps) 
                                               env)
                              (cdr exps)))))
      ;locals

      #|(locals-exp (names  exps l-body-exp l-body-exps)
                  (let* (
                         (args (eval-rands exps env))
                         (env (extend-env-recursively2 names args env))
                   )(let loop ((acc (eval-expression l-body-exp env))
                             (exps l-body-exps))
                    (if (null? exps) 
                        acc
                        (loop (eval-expression (car exps) 
                                               env)
                              (cdr exps))))
                    ))|#
      ;globals

       
              
      (else 'error-eval-expression)
      )    
    ))

(define listas-proc
  (lambda (exps list-ids list-bodies)
    (if (null? exps) (list list-ids list-bodies)
        (cases expression (car exps)
          (function-exp (texp ids body)
                    (listas-proc (cdr exps) (cons ids list-ids) (cons body list-bodies)))
          (else 'error-listas-proc)
             
             ))))

(define-datatype proc proc?
  (procedure
   (texps (list-of type-exp?))
   (ids (list-of symbol?))
   (exp expression?)))


(define make-boolean-list
  (lambda (zise bool)
    (if (equal? zise 0) '()
        (cons bool (make-boolean-list (- zise 1) bool)))))

            
;-----------------------------------------------------------------------------------------------




#|
prueba begin:

@x=100;
){
let(
@p=proc(@x) begin
set @x=add1(@x)
@x end;)
{/app(@p @x) + app(@p @x)/}}


let(
@p= proc @fac(@x) Si /@x == 0/ {1} sino {/@x * app(@fact /@x ~ 1/)/};
) {app(@p 5)}


letrec
@p= proc(@x) Si /@x == 0/ {1} sino {/@x * app(@p /@x ~ 1/)/}
in app(@p 5)


GLOBALS{
@x=5}
PROGRAM{
letrec
@p= function(@x) return Si /@x == 0/ {1} sino {/@x * app(@p /@x ~ 1/)/}
in app(@p @x)
}

GLOBALS{
@x=5
@p= function(@x)  return Si /@x == 0/ {1} sino {/@x * app(@p /@x ~ 1/)/}
}
PROGRAM{
BLOCK{
set @x=10
app(@p @x)
}}

GLOBALS{
@x=5
@p= function(@x)  return Si /@x == 0/ {1} sino {/@x * app(@p /@x ~ 1/)/}
}
PROGRAM{
LOCALS{
@x=10

}{app(@p @x)}}


GLOBALS{int @x=5 (int->int) @p=function(int @x) return @x } PROGRAM{app(@p @x)}

GLOBALS{ const int @x=5} PROGRAM{BLOCK{set @x=2 @x}}

GLOBALS{ const int @x=5} PROGRAM{set @x=2}

GLOBALS{var int @x=5 proc (int->int) @p=function(int @x) return @x } PROGRAM{@p}

 GLOBALS{
var int @x=5
proc (int->int) @p= function(int @x)  return Si /@x == 0/ {1} sino {/@x * app(@p /@x ~ 1/)/}
}
PROGRAM{app(@p @x)}

GLOBALS{
var int @x=5
proc (int->int) @p= function(int @x)  return Si /@x == 0/ {1} sino {/@x * app(@p /@x ~ 1/)/}

var list<int> @list= make-list(1 2 3)
}PROGRAM{ head(@list)}
|#