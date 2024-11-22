#lang eopl
;******************************************************************************************
;Andres David Ortega Arteaga 2241885
;Jose Daniel Trujillo Suarez 2225611

#|
INDICES DE BLOQUES DEL CODIGO
1) LEXIQUE-AND-SYNTANTIC-DEFINITIONS
2) APPLY-PRIMITIVES
3) AUTOMATIC-SLLGEN-FUNTIONS
4) INTERPRETE-FUNTIONS
5) PROCEDURES-FUNTIONS
6) ENVIRONMENTS-FUNTIONS
7) AUXILIAR-FUNTIONS
8) EXPRESSION-EVALUATOR
|#

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


;;                 ::= LOCALS { {type-exp assing}* }{expression {expression}* }
;;                     <LOCALS-exp defined-types assings first-exp exps>

;;                 ::= GLOBALS { {type-exp assing}* }{expression}
;;                     <global-exp defined-types assings main-body>

;;                 ::= funtion( ({type-exp identifier}*(,)) expression)
;;                 ::= <proc-exp arg-types ids body>

;;                 ::= ( ({expression}*(,)) )
;;                 ::= <list-exp args>

;;                 ::= [ ({expression}*(,)) ]
;;                 ::= <vect-exp args>

;;                 ::= { ({expression = expression}*(,)) }
;;                 ::= <dict-exp keys values>

;;                 ::= BLOCK{ expression {expression}*}
;;                 ::= <BLOCK-exp firs-exp exps>

;;                 ::= set var = expression
;;                 ::= <set-exp id expression>

;;                 ::= while ( expression ) do ( expression {expression}* )
;;                 ::= <whiele-exp test-exp firs-exp exps>

;;                 ::= for (identifier = expression; expression ; expression){expression {expression}*}
;;                 ::= <for-exp var var-exp stop-cond sumator first-exp exps>

;;                 ::= switch( expression ) {{case expression : expression}* default: expression}
;;                 ::= <switch-exp option cases cases-exps default-exp>

;;                 ::= print(expression)
;;                 ::= <exp>


;; <binary-primitive>  ::= + (primitive-sum)
;;                     ::= ~ (primitive-substract)
;;                     ::= / (primitive-div)
;;                     ::= * (primitive-mult)
;;                     ::= mod (primitive-mod)
;;                     ::= concat (primitive-con)
;;                     ::= > (primitive-greater)
;;                     ::= < (primitive-minor)
;;                     ::= >= (primitive-greater-equal)
;;                     ::= <= (primitive-minor-equal)
;;                     ::= != (primitive-diferent)
;;                     ::= == (primitive-comparator-equal)
;;                     ::= append (primitiva-append)
;;                     ::= ref-vector (primitiva-ref-vector)
;;                     ::= set-vector (primitiva-set-vector)
;;                     ::= append-vector (primitiva-append-vector)
;;                     ::= delete-val-pos (primitiva-delete-val-pos)
;;                     ::= ref-dict (primitiva-ref-dict)
;;                     ::= set-dict (primitiva-set-dict)

;; <unary-primitive>   ::= lenght (primitive-lenght)
;;                     ::= add1 (primitive-add1)
;;                     ::= sub1 (primirtive-sub1)
;;                     ::= neg (primitive-neg-boolean)
;;                     ::= empty? (primitive-empty)
;;                     ::= list? (primitive-list)
;;                     ::= head (primitive-head)
;;                     ::= tail (primitive-tail)
;;                     ::= keys-dict (primitive-keys-dict)
;;                     ::= values-dict (primitive-values-dict)
;;                     ::= make-list (make-l-primitive)
;;                     ::= make-vector (make-v-primitive)
;;                     ::= make-dict (make-d-primitive)

 
;; <types-exps>       ::= list<type-exp> (list-type-exp)
;;                    ::= (primitive ("zero?") zero-test-prim)    
;;                    ::= int int-type-exp)
;;                    ::= float (float-type-exp)
;;                    ::= String (String-type-exp)
;;                    ::= bool (bool-type-exp)
;;                    ::= void (void-type)
;;                    ::= ((separated-list type-exp "*") "->" type-exp ")") proc-type-exp)
;;                    ::= edge (edge-type-exp)
;;                    ::= edges  (edges-type-exp)
;;                    ::= vertices (vertices-type-exp)
;;                    ::= graph (graph-type-exp)
;;                    ::= (list<int>) (list-int-type)
;;                    ::= (list<float>) (list-float-type)
;;                    ::= (list<bool>) (list-bool-type)
;;                    ::= (list<strign>) (list-string-type)
;;                    ::= (vector<int>) (vector-int-type)
;;                    ::= (vector<float>) (vector-float-type)
;;                    ::= (vector<bool>) (vector-bool-type)
;;                    ::= (vector<strign>) (vector-string-type)
;;                    ::= (dict<string,int>) (dict-int-type)
;;                    ::= (dict<string,float>) (dict-float-type)
;;                    ::= (dict<string,bool>) (dict-bool-type)
;;                    ::= (dict<string,string>) (dict-string-type)

;******************************************************************************************
;******************************************************************************************


;----------LEXIQUE-AND-SYNTANTIC-DEFINITIONS---------------------------
;Especificación Léxica
(define scanner-spec-simple-interpreter
  '((white-sp
     (whitespace) skip)
    (comment
     ("%" (arbno (not #\newline))) skip)
    (identifier
     ("@" letter (arbno (or letter digit "?"))) symbol)
    (inmutable-identifier
     ("conts" "@" letter (arbno (or letter digit "?"))) symbol)
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
  '((program (expression) a-program)
    
    (expression (entero) lit-ent-exp)
    (expression (flotante) lit-float-exp)
    (expression (identifier) var-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)
    (expression ("list") empty-list-exp)
    ;(expression ("const" identifier) conts-exp)
    
    (expression 
     (unary-primitive "(" (arbno expression) ")")
     primapp-un-exp)
    
    (expression
     ( "app-b" "(" expression 
                  primitiva-binaria (arbno expression) ")")
     primapp-bin-exp)
    
    (expression
     ("\"" text "\"" )
     text-exp)

    (expression
     ("Si" expression "{" expression "}" "sino" "{" expression "}")
     if-exp)

    (expression
     ("declarar" "(" (arbno type-exp assing) ")"
                 "{"expression "}")
     localVar-exp)
    
    (expression
     ("LOCALS" "{" (arbno type-exp assing) "}"
               "{" expression (arbno expression)"}")
     LOCALS-exp)

    (expression ("GLOBALS" "{"(arbno type-exp assing)"}"
                           "PROGRAM" "{" type-exp "main()"
                           "{" expression "}" "}"
                           )
                global-exp)


    (expression
     ("funtion" "("(separated-list type-exp identifier ",") ")"
                expression )
     proc-exp)
    
    (expression
     ("app" expression "("(separated-list expression ",")")")
     app-exp)

    (expression ("letrec" (arbno type-exp identifier
                                 "(" (separated-list type-exp identifier ",") ")"
                                 "=" expression) "in" expression)
                letrec-exp)
  
    ;PARTES DE LAS LISTAS
    (expression
     ("(" (separated-list expression ",") ")")
     list-exp)
    
    ;PARTES DE VECTORES
    (expression ("["(separated-list expression ",")"]" ) vect-exp)

    ;PARTES DE DICCIONARIOS
    (expression ("{"(separated-list  expression ":" expression ",") 
                    "}") dict-exp)

    ;PARTES DE GRAFOS
    (expression ( "edge" "(" identifier "," identifier ")") edge-g-exp)
    
    (expression ( "edges" "(" (arbno expression ) ")" ) edges-g-exp)

    (expression ( "vers" "(" (separated-list identifier ",") ")") vertices-g-exp)

    (expression ( "graph" "(" expression "," expression ")" ";") graph-g-exp)


    (expression ("BLOCK" "{" expression (arbno expression )"}")
                BLOCK-exp)

    (expression ("set" var "=" expression)
                set-exp)

    (expression ("while" "(" expression ")" "do" "(" expression (arbno expression) ")")while-exp)

    (expression ( "for" "(" identifier "=" expression ";"
                        expression ";" expression ")"
                        "{"expression (arbno expression)"}")for-exp)
    
    (expression ( "switch" "(" expression ")" "{" (arbno "case" expression ":" expression ) "default:" expression "}")
                switch-exp )

    (expression ("print" "(" expression ")" ) print-exp)
    
    ; binary-Primitive-exp
    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("~") primitiva-resta)
    (primitiva-binaria ("/") primitiva-div)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("mod") primitiva-mod)
    (primitiva-binaria ("concat") primitiva-concat)
    (primitiva-binaria (">") primitiva-mayor)
    (primitiva-binaria ("<") primitiva-menor)
    (primitiva-binaria (">=") primitiva-mayor-igual)
    (primitiva-binaria ("<=") primitiva-menor-igual)
    (primitiva-binaria ("!=") primitiva-diferente)
    (primitiva-binaria ("==") primitiva-comparador-igual)
    (primitiva-binaria("append") primitiva-append)
    (primitiva-binaria("add-edge") primitiva-add-edge)
    (primitiva-binaria("vecinos-en") primitiva-vecinos-en)
    (primitiva-binaria("vecinos-sal") primitiva-vecinos-sal)
    (primitiva-binaria("ref-vector")primitiva-ref-vector)
    (primitiva-binaria("set-vector")primitiva-set-vector)
    (primitiva-binaria("append-vector")primitiva-append-vector)
    (primitiva-binaria("delete-val-pos")primitiva-delete-val-pos)
    (primitiva-binaria("ref-dict")primitiva-ref-dict)
    (primitiva-binaria("set-dict")primitiva-set-dict)
    
    ;;---------------------------

    
    ;unary-primitive-exp
    (unary-primitive ("length") primitive-lenght);operacion unaria para calcula longitud de un string
    (unary-primitive ("add1") primitive-add1);operacion unaria hallar el sucesor de un numero
    (unary-primitive ("sub1") primitive-sub1);operacion unaria hallar el predecesor de un numero
    (unary-primitive ("neg") primitive-neg-boolean);operacion que niega el valor de un booleano
    (unary-primitive("empty?") primitive-empty)
    (unary-primitive("list?") primitive-list)
    (unary-primitive("head") primitive-head)
    (unary-primitive("tail")primitive-tail)
    (unary-primitive("keys-dict")primitive-keys-dict)
    (unary-primitive("values-dict")primitive-values-dict)
    (unary-primitive("make-list") make-l-primitive)
    (unary-primitive("make-vector") make-v-primitive)
    (unary-primitive("make-dict") make-d-primitive)
    (unary-primitive("make-graph") make-g-primitive)
    (unary-primitive("edgess") primitiva-edges)
    (unary-primitive("vertices") primitiva-vertices)
    
    ;caracteristicas adicionales
    (type-exp ("list" "<" type-exp ">") list-type-exp)
    (primitive ("zero?") zero-test-prim)    
    (type-exp ("int") int-type-exp)
    (type-exp ("float") float-type-exp)
    (type-exp ("string") String-type-exp)
    (type-exp ("bool") bool-type-exp)
    (type-exp ("void") void-type)
    (type-exp ("(" (separated-list type-exp "*") "->" type-exp ")") proc-type-exp)
    (type-exp ("edge") edge-type-exp)
    (type-exp ("edges")  edges-type-exp)
    (type-exp ("vertices") vertices-type-exp)
    (type-exp ("graph")graph-type-exp)
    (type-exp ("list<int>") list-int-type)
    (type-exp ("list<float>") list-float-type)
    (type-exp ("list<bool>") list-bool-type)
    (type-exp ("list<string>") list-string-type)
    (type-exp ("vector<int>") vector-int-type)
    (type-exp ("vector<float>") vector-float-type)
    (type-exp ("vector<bool>") vector-bool-type)
    (type-exp ("vector<string>") vector-string-type)
    (type-exp("dict<string,int>") dict-int-type)
    (type-exp("dict<string,float>") dict-float-type)
    (type-exp("dict<string,bool>") dict-bool-type)
    (type-exp("dict<string,string>") dict-string-type)

    (var (identifier) mutable-var)
    (var ("conts" identifier) inmutable-var)
    (assing (var "=" expression ";") assing-exp)

    
    ))



;;-------------APPLY-PRIMITIVES---------------------------------------


;Funcion que resuelve las operaciones de cada primitiva binaria 
;apply-binary-primitive: <primitiva> <list-of-expression> -> numero
;apply-primitive: <primitiva> <list-of-expression> -> numero


(define apply-primitive-bin
  (lambda (prim-bin args)
    (cases primitiva-binaria prim-bin
      (primitiva-suma () (+ (car args) (cadr args)))
      (primitiva-resta () (- (car args) (cadr args)))
      (primitiva-div () (/ (car args) (cadr args)))
      (primitiva-multi () (* (car args) (cadr args)))
      
      (primitiva-mod () (if (and (integer? (car args)) (integer? (cadr args)))
                            (modulo (car args) (cadr args))
                            (real-modulo (car args) (cadr args))
                            )
                     )
      
      (primitiva-concat () (string-append (car args) (cadr args)))
      (primitiva-mayor () (valor-verdad? (comparar (car args) (cadr args) '>)))
      (primitiva-menor () (valor-verdad? (comparar (car args) (cadr args) '<)))
      (primitiva-mayor-igual () (valor-verdad? (comparar (car args) (cadr args) '>=)))
      (primitiva-menor-igual () (valor-verdad? (comparar (car args) (cadr args) '<=)))
      (primitiva-diferente () (valor-verdad? (not (eqv? (car args) (cadr args)))))
      (primitiva-comparador-igual () (valor-verdad? (equal? (car args) (cadr args))))
      (primitiva-add-edge() (if (> (length args)2)
                                (eopl:error "the expected number of arguments does not ~%
                                              match the given number~%
                                              expectend: 2~% given: ~s" (length args))
                                (add-edge (car args) (cases e-exp (cadr args)
                                                       (edge-exp (e1 e2)(list e1 e2))))
                                )
                         )

      (primitiva-vecinos-en() (if (> (length args)2)
                                (eopl:error "the expected number of arguments does not ~%
                                              match the given number~%
                                              expectend: 2~% given: ~s" (length args))
                                (non-empty-list
                                 (symbols->strings (vecinos-entrantes (car args) (cadr args))))
                                )
                           )
      
      (primitiva-vecinos-sal() (if (> (length args)2)
                                (eopl:error "the expected number of arguments does not ~%
                                              match the given number~%
                                              expectend: 2~% given: ~s" (length args))
                                (non-empty-list
                                 (symbols->strings (vecinos-salientes (car args) (cadr args))))
                                )
                           )
      
      (primitiva-append() (cond
                              ((and (vs-exp? (car args)) (vs-exp? (cadr args)))
                               (non-empty-list(append (extract-vertices (car args))
                                                      (extract-vertices (cadr args))))
                               )

                              ((and (es-exp? (car args)) (es-exp? (cadr args)))
                               (non-empty-list(append (extract-edges (car args))
                                                      (extract-edges (cadr args))))
                               )
                            
                              ((not(and (list? (car args)) (list? (cadr args))))
                              (non-empty-list (append (extract-values-list (car args))
                                                      (extract-values-list (cadr args)))))
                              (else(non-empty-list (append (car args) (cadr args))))    
                              )
                       )
      (primitiva-ref-vector()(if (vector? (car args))
                                 (vector-ref (car args) (cadr args))
                                 (vector-ref (extract-values-vec (car args))
                                             (cadr args))
                                 )
                           )
      (primitiva-set-vector()(if (vector? (car args))
                                 (vector-set! (car args) (cadr args))
                                 
                                 (let((vec (extract-values-vec (car args)))
                                      (pos&val (extract-values-list (cadr args)))
                                      )
                                   (vector-set! vec (car pos&val) (cadr pos&val))
                                   "cambio exitoso"
                                   )
                                 
                                 ))
      
      (primitiva-append-vector()(non-empty-vec (vector-append (car args) (cadr args))))

      (primitiva-delete-val-pos() (non-empty-vec(delete-val-pos (car args)(cadr args))))
      
      (primitiva-ref-dict() (ref-dict (car args) (cadr args)))

      (primitiva-set-dict() (set-dict (car args) (cadr args)))
      
      (else "faltan casos bianrio")                 
      )))

;Funcion que resuelve las operaciones de cada primitiva unaria
;apply-unary-primitive: <primitiva> <list-of-expression> -> numero
(define apply-unary-primitive
  (lambda (prim arg)
    (cases unary-primitive prim
      (primitive-lenght () (string-length arg))
      (primitive-add1 () (+ 1 arg))
      (primitive-sub1 () (- arg 1))
      (primitive-neg-boolean () (if (equal? arg "true") "false" "true"))

      (make-l-primitive () 
                        (cond
                          ((list? arg) (non-empty-list arg))
                          
                          ((lista? arg)
                           (cases lista arg
                             (empty-list() (empty-list))
                             (non-empty-list (l) l)))
                          ((or (number? arg) (string? arg))
                           (non-empty-list (list arg)))
                          (else "not valid argument")
                          )
                        )

      (make-v-primitive()
                       (if (lista? arg)
                           (non-empty-vec (list->vector (extract-values-list arg)))
                           (if (= (length arg) 2)
                               (non-empty-vec (make-vector (car arg) (cadr arg)))
                               (non-empty-vec (list->vector arg))
                               )                           
                           )
                       )

      (make-d-primitive ()
                        (cond
                          ((not(equal? (length arg) 2)) "Not valid aplicattion for make-dict")
                          ((and(null? (car arg)) (null? (cadr arg)))
                           (create-dict (list) (list)))
                          ((and (not(null? (car arg)))
                                (not(null? (cadr arg))))
                           (create-dict (car arg) (cadr arg))
                           )
                          )
                        )
      
      (make-g-primitive()
                       (if (> (length arg) 2)
                           (eopl:error "the expected number of arguments does not ~%
                                        match the given number~%
                                        expectend: 2~% given: ~s" (length arg))
                           (if (valid-rands-for-graph? (car arg)(cadr arg))
                               (if (and (lista? (car arg)) (lista? (cadr arg)))
                                   (graph-exp (vertices-exp(extract-values-list (car arg)))
                                               (edges-exp (convert-to-edges (extract-values-list (cadr arg)))))  
                                   (graph-exp (car arg) (cadr arg))
                                   )
                               
                               "Not valid aplication for make-graph"
                               )
                           )
                       )
      
      (primitiva-edges () (if (g-exp?  arg)
                              (cases g-exp arg
                                (graph-exp (vs es) es))
                              (if (list?  arg)
                                  (caddr arg)
                                  "Is not a graph"
                                  )
                              )
                       )

      (primitiva-vertices () (if (g-exp?  arg)
                              (cases g-exp arg
                                (graph-exp (vs es) vs))
                              (if (list?  arg)
                                  (cadr arg)
                                  "Is not a graph"
                                  )
                              )
                       )
      
      (primitive-empty () (cases lista arg (empty-list() "true")
                            (non-empty-list (vals) "false")(empty-list "true")))
                       
      (primitive-list () (cases lista arg (empty-list()"false")
                           (non-empty-list (vals) "true")(else "is not a list")))
      (primitive-head ()
                      (if (list? arg)
                          (car arg)
                          (car (extract-values-list arg))
                          ))
      (primitive-tail ()
                      (if (lista? arg)
                          (if (= (length (extract-values-list arg)) 1)
                              (empty-list)
                              (non-empty-list (cdr (extract-values-list arg)))
                              )         
                          (if (list? arg)
                              (if (= (length arg) 1)
                                  (list)
                                  (cdr arg)
                                  )
                              "Argument not is a list"
                              )
                          
                          )
                      )
      
      (primitive-keys-dict() (non-empty-list (keys-dict arg)))
      (primitive-values-dict()(non-empty-vec(values-dict arg)))
      (else "faltan casos unario")
      )))



;----------------AUTOMATIC-SLLGEN-FUNTIONS-----------------------------


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
                         (lambda (pgm) (begin
                                         (type-of-program  pgm)
                                         (eval-program pgm)
                                         )) 
                         (sllgen:make-stream-parser 
                          scanner-spec-simple-interpreter
                          grammar-simple-interpreter)))




;----------------------------INTERPRETE-FUNTIONS------------------------------------------------------



;eval-program: <programa> -> numero
;función que evalúa un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)
(define eval-program
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
                 (eval-expression body (init-env))))))

; funciones auxiliares para aplicar eval-expression a cada elemento de una 
; lista de operandos (expresiones)
(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

;funcion que aplica eval-expression a un solo elemento
(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))

;Funcion que define los valores de verdad, 0 = false y diferente de 0 = true
;true-value?: numero -> boolean
(define true-value?
  (lambda (x)
    (not (zero? x))))



;----------------------------PROCEDURES-FUNTIONS-----------------------------------

;define-datatype de los procedimientos
(define-datatype procval procval?
  (closure
   (ids (list-of symbol?))
   (body expression?)
   (env environment?)))


;Funcion que extiende un ambiente y evalua un procedimiento en ese nuevo ambiente extendido
;apply-procedure: <procedure> <list-of expression> -> numero
(define apply-procedure
  (lambda (proc args)
    (cases procval proc
      (closure (ids body env)
               (eval-expression body (extend-env ids args env))))))


;------------------------------ENVIRONMENTS-FUNTIONS-----------------------------

;ambiente inicial
(define init-env
  (lambda ()
    (extend-env
     '(@w @x @y @z @k @f)
     '(1 2 3 "hola" "FLP" (non-empty-pair 'a 'b) )
     (empty-env))))

;definición del tipo de dato ambiente
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vec vector?)
   (env environment?)))

;definicion de scheme-value
;cualquier cosa es un scheme-value
(define scheme-value? (lambda (v) #t))

;empty-env: -> enviroment
;función que crea un ambiente vacío
(define empty-env  
  (lambda ()
    (empty-env-record)));llamado al constructor de ambiente vacío 

;extend-env: <list-of symbols> <list-of numbers> enviroment -> enviroment
;función que crea un ambiente extendido
(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (list->vector vals) env)))

;extend-env-recursively: <list-of symbols> <list-of <list-of symbols>> <list-of expressions> environment -> environment
;función que crea un ambiente extendido para procedimientos recursivos
(define extend-env-recursively
  (lambda (proc-names idss bodies old-env)
    (let ((len (length proc-names)))
      (let ((vec (make-vector len)))
        (let ((env (extended-env-record proc-names vec old-env)))
          (for-each
           (lambda (pos ids body)
             (vector-set! vec pos (closure ids body env)))
           (iota len) idss bodies)
          env)))))
 
;extend-recursive-env (lisf-of symbols) <list-of expressions> <environment> -> environment
;Funcion que crea un ambiente extendido, si el identificador es una variable guarda la variable
;si es un procedimiento crea una closure y la guarda
(define extend-recursive-env
  (lambda (ids exps old-env)
    (let* ((len (length ids))
           (vec (make-vector len))
           (env (extended-env-record ids vec old-env)))
      (for-each
       (lambda (pos body)
         (if (procval? body)
             (let((ids-bodies (cases procval body (closure (ids body env)(list ids body)))))
               (vector-set! vec pos (closure (car ids-bodies) (cadr ids-bodies) env))
               )                  
             (vector-set! vec pos body))
         )            
       (iota len) exps)         
      env
      )
    )
  )


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
    (deref (apply-env-ref env sym))))

;(apply-env-ref env sym)))
;env))
(define apply-env-ref
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
                        (eopl:error 'apply-env-ref "No binding for ~s" sym))
      (extended-env-record (syms vals env)
                           (let* ((sym (if (inmutable-var? syms sym)
                                           (inmutable-var-convert sym)
                                           sym))
                                  (pos (rib-find-position sym syms)))
                             (if (number? pos)
                                 (a-ref pos vals)
                                 (apply-env-ref env sym)))))))

;***************************ENVIRONMENT-TYPE**************************************
(define-datatype type-environment type-environment?
  (empty-tenv-record)
  (extended-tenv-record
   (syms (list-of symbol?))
   (vals (list-of type?))
   (tenv type-environment?)))

(define empty-tenv empty-tenv-record)
(define extend-tenv extended-tenv-record)

;apply-tenv <environment> <symbol> -> type
;Funcion que busca el tipo de una variable en un ambiente de tipos 
(define apply-tenv 
  (lambda (tenv sym)
    (cases type-environment tenv
      (empty-tenv-record ()
                         (eopl:error 'apply-tenv "Unbound variable ~s" sym))
      (extended-tenv-record (syms vals env)
                            (let* ((sym (if (inmutable-var? syms sym)
                                            (inmutable-var-convert sym)
                                            sym))
                                   (pos (list-find-position sym syms)))
                              (if (number? pos)
                                  (list-ref vals pos)
                                  (apply-tenv env sym)))))))
;---------------------------AUXILIAR-FUNTIONS------------------------------------------

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


;Funcion que convierte a string numeros y simbolos
;convert-to-string: a => string
;usage: (convert-to-string a) => string a
(define convert-to-string
  (lambda (a)
    (cond
      ((number? a) (number->string a))
      ((symbol? a) (symbol->string a))
      (else a)
      )
    )
  )

;comparar-strings? <string> <string> -> bool
;Funcion que compara 2 strings de acuerdo con un indentificador dado
(define comparar-strings?
  (lambda (string1 string2 comparador)
    (cond
      [(equal? comparador '<) (string<? string1 string2)]
      [(equal? comparador '>) (string>? string1 string2)]
      [(equal? comparador '>=) (string>=? string1 string2)]
      [(equal? comparador '<=) (string<=? string1 string2)]
      [else (eopl:error "no se pueden comparar los strings")])))

;comparar-strings? <number> <number> -> bool
;Funcion que compara 2 numeros de acuerdo con un indentificador dado
(define comparar-numeros?
  (lambda (num1 num2 comparador)
    (cond
      [(equal? comparador '<) (< num1 num2)]
      [(equal? comparador '>) (> num1 num2)]
      [(equal? comparador '>=) (>= num1 num2)]
      [(equal? comparador '<=) (<= num1 num2)]
      [else (eopl:error "no se pueden comparar los numeros")])))        
    

;comparar <scheme-value> <scheme-value> -> boolç
;Funcion que recibe 2 valores y si ambos son ò strings ò numeros los compara
(define comparar
  (lambda (e1 e2 comparador)
    (cond
      [(and (string? e1) (string? e2)) (comparar-strings? e1 e2 comparador)]
      [(and (number? e1) (number? e2)) (comparar-numeros? e1 e2 comparador)]
      [else (eopl:error "valor esperado, dos strings o dos flotantes")])))
       


;Funcione que retorna true si una operacion binaria es verdadera, o false si
;la exprecion es falsa
;valor_verdad?: primitiva-binaria x expression x expression => number
;usage:(valor-verdad? prim exp1 exp2) => 1 si al aplicar la primitiva a
;los 2 argumentos el valor es diferente a 0, 0 de caso contrario
(define valor-verdad?
  (lambda (bool)
    (if bool "true" "false")))

;real-modulo <number> <number> -> number
;Funcion modulo para numeros reales
(define real-modulo
  (lambda (x y)
          (- x (* (truncate (/ x y)) y))
          )
  )

;progresive-env <list-of symbols> <list-of expression> <environment> -> environment
;Funcion que retorna un ambiente extendido en el cual la declaracion de una variable
;conoce a todas las variables predecesoras
(define progresive-env
  (lambda(ids exps env)
    (let*((len (length ids))
          (vec (make-vector len))
          (env (extended-env-record ids vec env))
          )
      
      (for-each
       (lambda (pos exps)
             (vector-set! vec pos (eval-expression exps env)))               
       (iota len) exps) 
      env
      )
    )
  )
;-------------------------LISTAS---------------------------------------
;datatype para representar las listas
(define-datatype lista lista?
  (empty-list)
  (non-empty-list (values list?))
  )

;extract-values-list <lista> -> <list>
;Funcion que extrae la list de valores de un datatype lista
(define extract-values-list
  (lambda (l1)
    (cases lista l1
      (empty-list()(list))
      (non-empty-list (values) values))
    )
  )

;-------------------------VECTORES---------------------------------
;datatype para representar vectores
(define-datatype vec vec?
  (empty-vec)
  (non-empty-vec (values vector?))
  )

;extract-values-vec <vec> -> <vector>
;Funcion que extrae el vector de valores de un datatype vec
(define extract-values-vec
  (lambda (vector)
    (cases vec vector
      (empty-vec()( #() ))
      (non-empty-vec (values) values))
    )
  )

;vector-append <vector> <scheme-value> -> vector
;Funcion que recibe un vector y un valor cualquiera y retorna un vector con el
;nuevo valor
(define vector-append
  (lambda (vector value)
    (let((l1 (vector->list (extract-values-vec vector)))
         (l2 (list value)))
      (list->vector (append l1 l2))
      )
    )
  )

;delete-val-pos <vector> <integer> -> vector
;Funcion que toma un vector y un entero y retorna un nuevo vector
;eliminando el elemento de la posicion dada y corriendo los elementos a la derecha
;del valor, una casilla a la izquierda.
(define delete-val-pos
  (lambda (vector pos)
    (let((delete-value (vector-ref (extract-values-vec vector) pos))
         (lista (vector->list(extract-values-vec vector))))
      (list->vector (delete-val-list lista delete-value))
      )
    )
  )

;delete-val-list <list> <scheme-value> -> <lista>
;Funcion auxiliar para eliminar un valor especifico de una lista
(define delete-val-list
  (lambda (lista value)
    (cond
      ((null? lista) empty)
      ((not(= (car lista) value))
       (cons (car lista) (delete-val-list (cdr lista) value)))
      ((and (= (car lista) value) (not(null? (cdr lista))))
       (cons (cadr lista) (delete-val-list (cddr lista) value))
       )
      (else empty)
      )
    )
  )

;----------------FUNCIONES PARA LOS DICCIONARIOS--------------------
;datatype para representar diccionarios
(define-datatype dictionary dictionary?
  (empty-dict)
  (non-empty-dict (keys list)
                  (values vector?))
  )

;create-dict <lista> <scheme-value> -> dict
;Funcion que toma una lista y un valor y crea un dict, el valor lo manipula dependiendo de si es
;una lista o un vec
(define create-dict
  (lambda (keys values)
    (let((keys1 (extract-values-list keys))
         (values1 (if (lista? values)
                      (list->vector (extract-values-list values))
                      (extract-values-vec values)
                      ))
         )
      
      (if (and (null? keys1) (= (vector-length values1)) 0)
          (empty-dict) 
          (non-empty-dict keys1 values1))
      )
    )
  )


;keys-dict <dict> -> list
;Funcio que extrae las keys de un dict
(define keys-dict
  (lambda (dict)
    (cases dictionary dict
      (empty-dict() "{}")
      (non-empty-dict (keys values)
                      keys)
      )
    )
  )

;values-dict <dict> -> vector
;Funcion que extrae los values de un dict
(define values-dict
  (lambda (dict)
    (cases dictionary dict
      (empty-dict() "{}")
      (non-empty-dict (keys values)
                      values)
      )
    )
  )

;ref-dict <dict> <scheme-value> -> scheme-value
;Funcion que retorna el valor de un key dentro de un dict si esta existe
(define ref-dict
  (lambda(dict key)    
    (let((pos (list-find-position key (keys-dict dict)))
         (vec-values (values-dict dict)))
      (vector-ref vec-values pos)
      )
    )
  )



;set-dict <dict> <scheme-value> -> string
;Funcion que cambiar el valor asocidado a una key en un diccionario
(define set-dict
  (lambda (dict values)
    (let((pos (list-find-position (car (extract-values-list values)) (keys-dict dict)))
         (vec-values (values-dict dict))
         )
      (vector-set! vec-values pos (cadr (extract-values-list values)))
      "cambio exitoso"
      )
    )
  )
;----------------GRAPHS------------------------------------------------
;datatypes para definir los grafos dirigidos
(define-datatype g-exp g-exp?
 (graph-exp (v vs-exp?)
        (g es-exp?)))

(define-datatype vs-exp vs-exp?
  (vertices-exp (v (list-of symbol?))))

(define-datatype es-exp es-exp?
  (edges-exp (e (list-of e-exp?))))

(define-datatype e-exp e-exp?
  (edge-exp (sym-left symbol?)
            (sym-right symbol?)))

;valid-rands-for-graph  <scheme-value> <scheme-value> -> bool
;Funcion que retorna 2 argumentos son validos para crear un grafo
(define valid-rands-for-graph?
  (lambda  (vs es)
    (if (or (and (vs-exp? vs) (es-exp? es)) (and (lista? vs) (lista? es)))
        #t
        #f
        )
  )
)

;vecino-prim? <primitiva unaria> -> bool
;Funcion que valida que sea una de las primitivas de vecinos de un grafo
(define vecino-prim?
  (lambda (prim)
    (cases primitiva-binaria prim
      (primitiva-vecinos-en()#t)
      (primitiva-vecinos-sal()#t)
      (else #f)
      )
    )
  )

;extract-vertices <vs-exp>-> <list-of symbols>
;Funcion que recibe un vs-exp y retorna la lista de los vertices
(define extract-vertices
  (lambda (vs)
    (cases vs-exp vs
      (vertices-exp (v)v)))
  )

;extract-edges <es-exp>-> <list-of <list-of-symbols>>
;Funcion que recibe un es-exp y retorna una list con las aristas de un grafo
(define extract-edges
  (lambda (es)
    (cases es-exp es
      (edges-exp (e)(map extract-eds e))))
  )

;extract-eds <ed-exp>-> <list-of symbols>
;Funcion que extra el edge de un ed-exp
(define extract-eds
  (lambda (ed)
    (cases e-exp ed
      (edge-exp (l r) (list l r))))
)

;conver-to-edges <list-of <list-of symbols>> -> <list-of ed-exp>
;Funcio que toma un list de tuplas y retorna una list con las tuplas
;convertidas en ed-exp
(define convert-to-edges
  (lambda (edges)    
  (map
   (lambda (ed)
    (edge-exp (car ed) (cadr ed))) edges)

  )
)

;extract-value <identifier> -> symbol
;Funcion que recibe un identificardor y retorna su id
(define extract-value
  (lambda (exp)
    (cases expression exp
      (var-exp(id)id)
      (else "not is a var-exp"))
    )
  )


; symbols->strings <list-of symbols> -> <list-of strings>
;Funcion que recibe una list de symbols y retorna una list con los
;symbols convertidos en strings
(define symbols->strings
  (lambda (l)
    (map symbol->string l))
)

;;add-edges-dtype:g-exp x List-> g-exp
;;usage: (add-edges-dtype grafo e)= resive un g-exp y una arista en forma de lista y si la arista no esta en las aristas del grafo entonces la funcion
;;crea un nuevo grafo con la arista insertada en el.
(define add-edge
  (lambda (grafo e)
    (let*(
          (ed-ex (edge-exp (car e) (cadr e)))
          (vertices-expresion (cases g-exp grafo (graph-exp (v e) v)))
          (edges-expresion (cases g-exp grafo (graph-exp (v e) e)))
          (edges-list (cases es-exp edges-expresion ( edges-exp (l) l)))
          (new-edge-list (if (not (is-in-edges? edges-list ed-ex))
                             (insertar-edge ed-ex edges-list)
                             edges-list
                             )
                         )
          (new-graph (graph-exp vertices-expresion (edges-exp new-edge-list)))
          )new-graph
      )
    )
  )

;;is-in-edges?:List x e-exp ->Bool
;;usage:(is-in-edges? edges edge )= resive una lista de e-exp y un e-exp y verifica que ese e-exp este en la lista, si esta retorna true
;;de lo contrario retorna falso. Se usa para verificar que la arista en la funcion add-edge no este dentro de la lista de e-exp del grafo de tipo g-exp.
;;<List> ::= ()
;;::= (<Bool> <List>)
(define is-in-edges?
  (lambda (edges edge)
    (if(null? edges)
       #f
       (let(
            (a (cases e-exp edge (edge-exp (a b) a)))
            (b (cases e-exp edge (edge-exp (a b) b)))
            (c (cases e-exp (car edges) (edge-exp (c d) c)))
            (d (cases e-exp (car edges) (edge-exp (c d) d)))
            )(or (and (eqv? a c) (eqv? b d))
                 (is-in-edges? (cdr edges) edge))
         ))
    )
  )

;;insertar-edge: List x e-exp ->List
;;usage: (isertar-edge edge edges)= resive  una arista de tipo e-exp y una lista de aristas de tipo e-exp e inserta la arista al final de esta lista. Se usa en la funcion add-edge
;;para insertar la arista .
;;<List> ::= ()
;;::= (<e-exp> <List>)
(define insertar-edge
  (lambda(edge edges)
    (if (null? edges)
        (list edge)
        (cons (car edges) (insertar-edge edge (cdr edges)))
        )
    )
  )

;;vecinos-entrantes:g-exp x List->g-exp
;;usage:(vecinos-entrantes grafo a) = resive un grafo de tipo g-exp y un vertice. retorna una lista con los nodos desde los cuales se pueden llegar al nodo dado.

;;funcion auxiliar

;;buscar-lp: List x symbol ->List
;;usage: (buscar-lp a list-edges) = busca los nodos desde los cuales se puede llegar al nodo a.
;;<List> ::= ()
;;::= (<symbol> <List>)
(define vecinos-entrantes
  (lambda (grafo a )
    (cases g-exp grafo
      (graph-exp (v e)
                 (letrec(

                         (list-edges (cases es-exp e (edges-exp (l) l)))
                         (buscar-lp
                          (lambda (a lp)
                            (if (null? lp)
                                empty
                                (let*(
                                    (x (cases e-exp (car lp) (edge-exp (a b) a)))
                                    (y (cases e-exp (car lp) (edge-exp (a b) b)))
                                    (respuesta (if (eqv? a y) 
                                    (cons x (buscar-lp a (cdr lp)))
                                    (buscar-lp a (cdr lp))

                                    ))
                                    )
                                  respuesta
                                  )
                                )
                            )
                          )
                         )
                   (buscar-lp a list-edges)
                   )
                 )
      )
    )
  )

;;vecinos-salientes:g-exp x List->g-exp
;;usage:(vecinos-salientes grafo a) = resive un grafo de tipo g-exp y un vertice. retorna una lista con los nodos  a los cuales
;;se puede llegar desde el nodo dado.

;;funcion auxiliar

;;buscar-lp: List x symbol ->List
;;usage: (buscar-lp a list-edges) = busca los nodos a los cuales se puede llegar desde el nodo a.
;;<List> ::= ()
;;::= (<symbol> <List>)
(define vecinos-salientes
  (lambda (grafo a )
    (cases g-exp grafo
      (graph-exp (v e)
                 (letrec(
                         (list-edges (cases es-exp e (edges-exp (l) l)))
                         (buscar-lp
                          (lambda (a lp)
                            (if (null? lp)
                                empty
                                (let*(
                                    (x (cases e-exp (car lp) (edge-exp (a b) a)))
                                    (y (cases e-exp (car lp) (edge-exp (a b) b)))
                                    (respuesta (if (eqv? a x) 
                                    (cons y (buscar-lp a (cdr lp)))
                                    (buscar-lp a (cdr lp))
                                    ))
                                    )
                                  respuesta
                                  )
                                )
                            )
                          )
                         )
                   (buscar-lp a list-edges)
                   )
                 )
      )
    )
  )
;----------------BLOCK-AND-SET-FUNTIONS--------------------------------
;id-var <assing-exp> -> symbol
;Funcion que retorna la id de una exprecion de asignacion
(define id-var
  (lambda(exp)
    (cases assing exp
      (assing-exp (id exp)  id)
      )
    )
  )

;exp-var <assing-exp> -> expression
;Funcion que retorna la expression de un exprecion de asignacion
(define exp-var
  (lambda(exp)
    (cases assing exp
      (assing-exp (id exp)  exp)
      )
    )
  )


;eval-var <var-exp> -> symbol
;Funcion que recibe un var-exp y retorna la representacion, si es mutable retorna l id
;si no es mutable retorna la id antecedida con la palabra conts
(define eval-var
  (lambda (variable)
    (cases var variable
      (mutable-var (id) id)
      (inmutable-var (id) (string->symbol(string-append "conts" (symbol->string id))))
      ))
  )

;caracter-index <string> -> bool or number
;Funcion que recibe un string y retorna la posicion en la cual se encuentra el caracter
;@, si no lo encuentra retorna #f
(define caracter-index
  (lambda (string)
    (let loop ((index 0))
      (cond
        ((= index (string-length string)) #f)
        ((char=? (string-ref string index) #\@) index)
        (else (loop (+ index 1)))
        )
      )
    )
  )

;comparar-symbol <symbol> <symbol> -> bool
;Funcion que recibe 2 symbolos y los compara, ambos deben contener el caracter @
;si el primer symbol inicia con la palabra conts verifica si son iguales despues de la @
;si no inicia con conts retorna #f
(define comparar-symbol
  (lambda (simbolo1 simbolo2)
    (let* ((cadena1 (symbol->string simbolo1))
           (cadena2 (symbol->string simbolo2))
           (indice1 (caracter-index cadena1))
           (indice2 (caracter-index cadena2)))
      (if (and indice1 
               indice2
               (string-prefix? "conts" cadena1))
          (string=? (substring cadena1 (+ indice1 1))
                    (substring cadena2 (+ indice2 1)))
          #f)
      )
    )
  )

;inmutable-var? <list-of symbol> <symbol> -> bool
;Funcion que recibe un symbolo y le añade la palabra conts al inicio
;y verifica si el nuevo symbolo esta en una lista
(define inmutable-var?
  (lambda (list sym)
    (let((const-sym (string->symbol(string-append "conts" (symbol->string sym)))))
      (if (list? (member const-sym list))
          #t
          #f
          )
      )
    )
  )

;inmutable-var-conver <symbol> -> symbol
;Funcion que recibe un symbol y le añade la palabra conts al inicio
(define inmutable-var-convert
  (lambda (sym)
    (string->symbol(string-append "conts" (symbol->string sym)))
    )
  )

;inmutable-var-id <symbol> -> symbol
;Funcion que recibe una inmutable-var y retorna su id
(define inmutable-var-id
  (lambda (sym)
    (let*((cadena (symbol->string sym))
          (indice (caracter-index cadena))
          )
      (string->symbol(substring cadena indice)))
    )
  )

;string-prefix? <string> <string> -> bool
;Funcion que recibe un prefijo(string) y una cadena(string) y verifica
;si la cadena inicia con el prefijo dado
(define string-prefix?
  (lambda (prefijo string)
    (and (>= (string-length string) (string-length prefijo)) 
         (string=? (substring string 0 (string-length prefijo)) prefijo))
    )
  )


;symbols-env <environment> -> <list-of symbols>
;Funcion que extrae la list de symbols de un environment
(define symbols-env
  (lambda (env)
    (cases environment env
      (empty-env-record ()(list))
      (extended-env-record (syms vals env) (append syms (symbols-env env)))
      )
    )
  )
;----------------EXPRESSION-EVALUATOR----------------------------------

;*****************References****************************************
;datatypes para las referencias
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


;eval-expression: <expression> <enviroment> -> numero
;evalua la expresión en el ambiente de entrada
(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (lit-ent-exp (datum) datum)
      (lit-float-exp (datum) datum)
      (var-exp (id) (apply-env env id))
      ;(conts-exp (id) (apply-env env id))
      (text-exp (text) text)
      (true-exp () "true")
      (false-exp () "false")
      (empty-list-exp () (empty-list))

      (edge-g-exp (v1 v2) (edge-exp v1 v2))
      (edges-g-exp (edges) (edges-exp (eval-rands edges env)))
      (vertices-g-exp (vers) (vertices-exp vers))
      (graph-g-exp (vers edges) (graph-exp vers edges))
      
      (primapp-un-exp (prim rand)
                      (let ((arg (if (> (length rand) 1)
                                     (eval-rands rand env)
                                     (eval-expression (car rand) env)
                                     )))
                        (apply-unary-primitive prim arg)                       
                        ))
      
      (primapp-bin-exp (exp1 prim exp2)
                       (let ((arg1 (eval-expression exp1 env))
                             (arg2 (if (equal? (length exp2) 2)
                                           (non-empty-list (list (eval-expression (car exp2) env)
                                                             (eval-expression (cadr exp2) env)))
                                       (if (vecino-prim? prim)
                                           (extract-value (car exp2))
                                           (eval-expression (car exp2) env))))
                             )
                         (apply-primitive-bin prim (list arg1 arg2))
                         )
                       )

      (if-exp(test-exp true-exp false-exp)
             (if(equal? (eval-expression test-exp env) "true")
                (eval-expression true-exp env)
                (eval-expression false-exp env)))

      (localVar-exp(types exps body)
                   (let ((args (eval-rands (map exp-var exps) env))
                         (ids (map eval-var (map id-var exps))))
                     (eval-expression body
                                      (extend-env ids args env))
                     ))

      (proc-exp (ids-types ids body)
                (closure ids body env))

      (app-exp (rator rands)
               (let (
                     (proc (eval-expression rator env))
                     (args (eval-rands rands env)))
                 (if (procval? proc)
                     (apply-procedure proc args)
                     proc
                     )
                 )
               )
      
      (letrec-exp (type-proc proc-names arg-types args proc-bodies letrec-body)
                  (eval-expression letrec-body
                                   (extend-env-recursively proc-names args proc-bodies env))
                  )
      
      (list-exp (args)
                (if (null? (eval-rands args env))
                    (empty-list)
                    (non-empty-list (eval-rands args env))
                    )
                )

      (vect-exp (args)
                (if (null? (eval-rands args env))
                    (empty-vec)
                    (non-empty-vec (list->vector (eval-rands args env)))
                    )
                )

      (dict-exp (keys values)                
                (non-empty-dict (eval-rands keys env)
                                (list->vector (eval-rands values env)))
                )
      
      (set-exp (id rhs-exp)
               (let((id (eval-var id)))
                 (if (number? (rib-find-position id (symbols-env env)))
                     (begin 
                       (setref!
                        (apply-env-ref env id)
                        (eval-expression rhs-exp env))
                       1)
                     (eopl:error  "Attempt to change the value of an immutable variable")
                     )
                 )              
               )

      (BLOCK-exp (exp exps) 
                 (let loop ((acc (eval-expression exp env))
                            (exps exps))
                   (if (null? exps) 
                       acc
                       (loop (eval-expression (car exps) env)
                             (cdr exps)))))

      (LOCALS-exp(ids-types exps first-instruct instructions)
                 (let*(
                       (ids (map eval-var (map id-var exps)))
                       (exps (map exp-var exps))                      
                       (env (progresive-env ids exps env))
                       )
                   
                   (let loop ((acc (eval-expression first-instruct env))
                              (exps instructions))                    
                     (if (null? exps) 
                         acc
                         (loop (eval-expression (car exps) env)
                               (cdr exps))))
                   
                   )
                 )
      
      (global-exp(types exps type-body main-body)
                 (let*(
                       (ids (map eval-var (map id-var exps)))
                       (ids-bodies (eval-rands (map exp-var exps) env))
                       (global-env (extend-recursive-env ids ids-bodies env))
                       )
                   (begin
                   (eval-expression main-body global-env))
                   )
                 )



      (while-exp (test-exp first-exp exps)
                 (let while ((t-exp (eval-expression test-exp env)))
                   (if (equal? t-exp "true")
                       (begin
                         (let loop ((acc (eval-expression first-exp env))
                                    (exps exps))                    
                           (if (null? exps) 
                               acc
                               (loop (eval-expression (car exps) env)
                                     (cdr exps))))
                         (while (eval-expression test-exp env)))
                       "fin del bucle"
                       )
                   )
                 )
      
      (for-exp (id beginning stop-cond sumator first-exp exps)
               (let*((vec (list->vector (list (eval-expression beginning env))))
                     (env (extended-env-record (list id) vec env)))
                 (let ciclo()                 
                   (let ((stop (eval-expression stop-cond env)))
                     (if (equal? stop "true")
                         (begin
                           (let loop ((acc (eval-expression first-exp env))
                                      (exps exps))                    
                             (if (null? exps) 
                                 acc
                                 (loop (eval-expression (car exps) env)
                                       (cdr exps))))
                           (eval-expression sumator env)
                           (ciclo))
                         "fin del ciclo"
                         )
                     )
                   )
                 )
               )

      (switch-exp (option coincidences coincidences-exps default-exp)
                  (let((coincidence-exp (coincidence-case
                                         (eval-expression option env)
                                         (eval-rands coincidences env)
                                         coincidences-exps)))
                    (if (string? coincidence-exp)
                           (eval-expression default-exp env)
                           (eval-expression coincidence-exp env))
                    )
                  )
      (print-exp (exp)
                 (begin
                 (display (eval-expression exp env))
                 (newline)
                 "fin del print"
                  ))
      
      (else "faltan casos eval-expression")
      )    
    ))


;-----------------------------------------------------------------------------------------------
;----------------------------------TIPOS--------------------------------------------------------
;-----------------------------------------------------------------------------------------------


;*********************************DEFINITION******************************************************
;*************************************************************************************************
(define-datatype type type?
  (atomic-type
   (name symbol?))
  (proc-type
   (arg-types (list-of type?))
   (result-type type?))
  (structure-type
   (name symbol?)
   (types (list-of symbol?)))
  )

(define int-type
  (atomic-type 'int))

(define bool-type
  (atomic-type 'bool))

(define float-type
  (atomic-type 'float))

(define string-type
  (atomic-type 'string))

(define edge-type
  (structure-type 'edge '(string)))

(define edges-type
  (structure-type 'edges '(string)))

(define vertices-type
  (structure-type 'vertices '(string)))

(define graph-type
  (structure-type 'graph '(string string)))

(define empty-type
  (atomic-type 'empty))

(define empty-list-type
  (structure-type 'list '(empty)))

(define int-list-type
  (structure-type 'list '(int)))

(define float-list-type
  (structure-type 'list '(float)))

(define bool-list-type
  (structure-type 'list '(bool)))

(define string-list-type
  (structure-type 'list '(string)))

(define int-vect-type
  (structure-type 'vect '(int)))

(define float-vect-type
  (structure-type 'vect '(float)))

(define bool-vect-type
  (structure-type 'vect '(bool)))

(define string-vect-type
  (structure-type 'vect '(string)))

(define int-dict-type
  (structure-type 'dict '(string int)))

(define float-dict-type
  (structure-type 'dict '(string float)))

(define bool-dict-type
  (structure-type 'dict '(string bool)))

(define string-dict-type
  (structure-type 'dict '(string string)))

(define generic-dict-type
  (structure-type 'dict '(string generic)))

(define generic-structure-type
  (structure-type 'struct '(generic)))

;--------------------------Variables para los  tipos de expreciones que----------------
;--------------------------tienen varios tipos-----------------------------------------
(define proc-types-list
  (list
   (proc-type (list int-list-type) bool-type)
   (proc-type (list float-list-type) bool-type)
   (proc-type (list bool-list-type) bool-type)
   (proc-type (list string-list-type) bool-type))
  )

(define basic-aritmetic-types
  (list
   (proc-type (list int-type int-type) int-type)
   (proc-type (list int-type float-type) float-type)
   (proc-type (list float-type int-type) float-type)
   (proc-type (list float-type float-type) float-type))
  )

(define basic-logical-types
  (list
   (proc-type (list string-type string-type) bool-type)
   (proc-type (list bool-type bool-type) bool-type)
   (proc-type (list int-type int-type) bool-type)
   (proc-type (list int-type float-type) bool-type)
   (proc-type (list float-type int-type) bool-type)
   (proc-type (list float-type float-type) bool-type))
  )


;Funcion que convierte los type-exp en types
(define expand-type-expression
  (lambda (texp)
    (cases type-exp texp
      (int-type-exp () int-type)
      (bool-type-exp () bool-type)
      (String-type-exp()string-type)
      (float-type-exp ()float-type)
      (void-type() (atomic-type 'void))
      (edge-type-exp () edge-type)
      (edges-type-exp () edges-type)
      (vertices-type-exp () vertices-type)
      (graph-type-exp () graph-type)
      (list-int-type () int-list-type)
      (list-float-type () float-list-type)
      (list-bool-type () bool-list-type)
      (list-string-type () string-list-type)
      (vector-int-type () int-vect-type)
      (vector-float-type () float-vect-type)
      (vector-bool-type () bool-vect-type)
      (vector-string-type () string-vect-type)
      (dict-int-type() int-dict-type)
      (dict-float-type() float-dict-type)
      (dict-bool-type() bool-dict-type)
      (dict-string-type() string-dict-type)
      (proc-type-exp (arg-texps result-texp)
                     (proc-type
                      (expand-type-expressions arg-texps)
                      (expand-type-expression result-texp)))
      (else "faltan casos de tipos")
      )
    )
  )

;Funcion que mapea expand-type-expression a una lista de tipos
(define expand-type-expressions
  (lambda (texps)
    (map expand-type-expression texps)))


;********************************CHECKER-OF-PROGRAM-TYPE************************************************
;type-of-program: <programa> -> type
;función que chequea el tipo de un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp) (type-of-expression exp (empty-tenv))))))

;eval-expression: <expression> <enviroment> -> type
; chequea el tipo de la expresión en el ambiente de entrada
(define type-of-expression
  (lambda (exp tenv)
    (cases expression exp
      (lit-ent-exp (number)
                   int-type)
      (lit-float-exp (number)
                     float-type)
      (text-exp(text)
               string-type)
      
      (true-exp ()
                bool-type)
      (false-exp ()
                 bool-type)

      (empty-list-exp() empty-list-type)
      
      (var-exp (id)
               (apply-tenv tenv id)
               )

      (edge-g-exp (v1 v2) edge-type)
      
      (edges-g-exp (edges) edges-type)
      
      (vertices-g-exp (vers) vertices-type)
      
      (graph-g-exp (vers edges) (if (and (check-equal-type! (type-of-expression vers)
                                                             vertices-type vers)
                                         (check-equal-type! (type-of-expression edges)
                                                            edges-type edges))
                                    (graph-type)
                                    (eopl:error "Bab values types por endges and vertices")
                                    )
                   )

      (primapp-un-exp(prim rand)
                     (let* ((rand-type (if (> (length rand) 1)
                                           (types-of-expressions rand tenv)
                                           (type-of-expression (car rand) tenv)))
                            (cases (type-of-un-primitive prim))
                            (primitive  (cond((and (list? rand-type) (equal? (length rand-type) 2)
                                                   (or (equal? (unary-exeption-prim? prim) "vector-prim")
                                                       (equal? (unary-exeption-prim? prim) "dict-prim")))
                                              (match-binary-prim-type (car rand-type) (cadr rand-type) cases))
                                             
                                             ((and (list? rand-type) (> (length rand-type) 2))
                                              (match-unary-prim-type (type-of-structure rand-type)cases))

                                             (else
                                              (match-unary-prim-type rand-type cases))
                                             ))
                            (args-types-length (extrac-args-types-proc primitive))
                            )
                      
                       (cond((equal? (length args-types-length) 2)
                             (type-of-application
                              primitive
                              (list (car rand-type) (cadr rand-type))
                              prim (list (car rand) (cadr rand)) exp)
                             )

                            ((and (list? rand-type)(equal? (length args-types-length) 1))
                             (type-of-application
                              primitive
                              (list (car rand-type))
                              prim (list (car rand)) exp))

                            (else
                             (type-of-application
                              primitive
                              (list  rand-type)
                              prim (list (car rand)) exp))
                            )                
                       )                    
                     )

      (primapp-bin-exp (rand1 prim rand2)
                       (let*((rand-type1 (type-of-expression rand1 tenv))
                             (rand-type2 (if (equal? (length rand2) 2)
                                             (list (type-of-expression (car rand2) tenv)
                                                   (type-of-expression (cadr rand2) tenv))
                                             (type-of-expression (car rand2) tenv)))
                             (cases (type-of-bin-primitive prim))
                             (primitiva (if (and (list? rand-type2) (equal? (length rand-type2) 2))
                                            (match-binary-prim-exeption-type
                                             rand-type1 (car rand-type2) (cadr rand-type2) cases)
                                            (match-binary-prim-type
                                             rand-type1 rand-type2 cases))))

                         (if (equal? (length rand2) 2)
                             (type-of-application
                              primitiva
                              (types-of-expressions (list rand1 (car rand2) (cadr rand2)) tenv)
                              prim (list rand1 (car rand2) (cadr rand2)) exp)
                             
                             (type-of-application
                              primitiva
                              (types-of-expressions (list rand1 (car rand2)) tenv)
                              prim (list rand1 rand2) exp)
                             )
                         ) 
                       )
      
      (list-exp (args)
                (let*((types-list (types-of-expressions args tenv))
                      (type-of-struct (type-of-structure types-list)))
                  (if (cases type type-of-struct
                        (atomic-type(n)#t)
                        (else #f))
                      (structure-type 'list (list (atomic-type-value type-of-struct)))
                      type-of-struct
                      )
                  
                  )               
                )

      (vect-exp(args)
               (let*((types-list (types-of-expressions args tenv))
                     (type-of-struct (type-of-structure types-list)))
                 (structure-type 'vect (list (atomic-type-value type-of-struct)))
                 )
               )

      (dict-exp(keys values)
               (let*(
                     (keys-types (types-of-expressions keys tenv))
                     (values-types (types-of-expressions values tenv))
                     (keys-type-checked-converted
                      (atomic-type-value (type-of-structure keys-types)))
                     (type-struct (type-of-structure values-types))
                     (values-type-checked-converted
                      (if (cases type type-struct
                          (atomic-type(n)#t)
                          (else #f))
                          (atomic-type-value (type-of-structure values-types))
                          type-struct
                          )
                      )
                     )
                 (if (cases type type-struct
                        (atomic-type(n)#t)
                        (else #f))
                     (structure-type 'dict (list keys-type-checked-converted
                                             values-type-checked-converted))
                     generic-dict-type
                     )
                 
                 )
               )
      
      (if-exp (test-exp true-exp false-exp)
              (let ((test-type (type-of-expression test-exp tenv))
                    (false-type (type-of-expression false-exp tenv))
                    (true-type (type-of-expression true-exp tenv)))
                (check-equal-type! test-type bool-type test-exp)
                (check-equal-type! true-type false-type exp)
                true-type))

      
      (localVar-exp (ids-types exps body)
                    (let*(
                          (ids (map eval-var (map id-var exps)))
                          (exps (map exp-var exps))
                          (defined-types (eval-defined-types ids-types))                       
                          (tenv-extend (extended-tenv-record ids defined-types tenv))
                          (exps-types (types-of-expressions exps tenv-extend))
                          )
                      (begin
                        (for-each
                         check-equal-type!
                         defined-types exps-types ids)
                        (type-of-expression body tenv-extend))
                     
                      )
                    )
      
      (LOCALS-exp (ids-types exps first-instruct instructs)
                  (let*(
                        (ids (map eval-var (map id-var exps)))
                        (exps (map exp-var exps))
                        (defined-types (eval-defined-types ids-types))                       
                        (tenv-extend (extended-tenv-record ids defined-types tenv))
                        (exps-types (types-of-expressions exps tenv-extend))
                        )
                    (begin
                      (for-each
                       check-equal-type!
                       defined-types exps-types exps)
                      (return-last-type first-instruct instructs tenv-extend))
                    )
                  )


      (global-exp (ids-types exps type-body main-body)
                  (let*(
                        (ids (map eval-var (map id-var exps)))
                        (exps (map exp-var exps))
                        (defined-types (eval-defined-types ids-types))                       
                        (tenv-extend (extended-tenv-record ids defined-types tenv))
                        (exps-types (types-of-expressions exps tenv-extend))
                        (main-type (type-of-expression main-body tenv-extend))
                        (defined-main-type (expand-type-expression type-body))
                        )                   
                    (begin
                      (for-each
                       check-equal-type!
                       defined-types exps-types exps)
                      (check-equal-type! defined-main-type main-type main-body)
                       main-type
                      )
                    )
                  )
      
      (proc-exp (texps ids body)
                (type-of-proc-exp texps ids body tenv))

      
      (app-exp (rator rands)
               (type-of-application
                (type-of-expression rator tenv)
                (types-of-expressions rands tenv)
                rator rands exp))
                 
      (letrec-exp (result-texps proc-names texpss idss bodies letrec-body)
                  (type-of-letrec-exp result-texps proc-names texpss idss bodies
                                      letrec-body tenv))
      
      (set-exp (id new-exp)
               (let((id (eval-var id)))
                 (if (check-equal-type! (apply-tenv tenv id)
                                        (type-of-expression new-exp tenv)
                                        new-exp)
                     (apply-tenv tenv id)
                     "Types don't macth in set-exp"
                     )
                 )
               )

      (BLOCK-exp (first-instruct instructs)
                 (return-last-type first-instruct instructs tenv)                  
                 )
      
      (while-exp (test-exp first-exp exps)
                 (let ((test-type (type-of-expression test-exp tenv)))
                   (begin (check-equal-type! test-type bool-type test-exp)
                          (return-last-type first-exp exps tenv)
                          )
                   )       
                 )
      
      (for-exp (id beginning stop-cond sumator first-exp exps)
               (if (and (correct-beginning? id beginning)
                        (correct-stop-cond? stop-cond)
                        (correct-sumator? sumator))
                   (return-last-type first-exp exps tenv)
                   (eopl:error "bab value for inicializators in for-exp")
                   )
               )

      (switch-exp (option coincidences coincidence-exps default-exp)
                  (if (valid-option? option)
                      (let*(
                            (op-type (type-of-expression option tenv))
                            (cases (types-of-expressions coincidences tenv))
                            (cases-type (type-of-structure cases))
                            (coincidence-exp(coincidence-case
                                             (eval-expression option (empty-env))
                                             (eval-rands coincidences (empty-env))
                                             coincidence-exps)))
      
                        (if (check-equal-type! op-type cases-type option)
                            (if (string? coincidence-exp)
                                (type-of-expression default-exp tenv)
                                (type-of-expression coincidence-exp tenv)    
                                )
                            "type of option and cases didn't match"
                            )
                        )
                      "Is not a valid option for switch"
                      )
                  )
      (print-exp (exp)
                 (atomic-type 'void))
      
      (else "NO HAY TIPO")
      )
    )
  )

;***************************FUNTIONS-FOR-TYPES****************************************
;*************************************************************************************

;check-equal-type!: <type> <type> <expression> -> 
; verifica si dos tipos son iguales, muestra un mensaje de error en caso de que no lo sean
(define check-equal-type!
  (lambda (t1 t2 exp)
    (if (not (equal? t1 t2))
        (eopl:error 'check-equal-type! 
                    "Types didn’t match: ~s != ~s in~%~s"
                    (type-to-external-form t1)
                    (type-to-external-form t2)
                    exp
                    )
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
                  (list (type-to-external-form result-type))))
      (structure-type (name args)
                      (if (equal? name 'dict)
                          (string-append (symbol->string name) "<"(symbol->string (car args))
                                         "," (symbol->string (cadr args)) ">")
                          (string-append (symbol->string name) "<"(symbol->string (car args))">")
                          )
                      )
      (else "falta external form")
      )
    )
  )

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
        (proc-type arg-types result-type)
        ))))

;type-of-application: <type> (list-of <type>) <symbol> (list-of <symbol>) <expresion> -> <type>
;función auxiliar para determinar el tipo de una expresión de aplicación
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
                   rator (type-to-external-form rator-type))))
    )
  )

;type-of-primitive: <primitive> -> <type>
; función auxiliar para determinar el tipo de una primitiva
(define type-of-un-primitive
  (lambda (prim)
    (cases unary-primitive prim
      (primitive-lenght ()
                        (proc-type (list string-type) int-type))
      
      (primitive-add1 ()
                      (list
                       (proc-type (list int-type) int-type)
                       (proc-type (list float-type) float-type)
                       ))
      
      (primitive-sub1 ()
                      (list
                       (proc-type (list int-type) int-type)
                       (proc-type (list float-type) float-type)
                       ))
      
      (primitive-neg-boolean()
                            (proc-type (list bool-type) bool-type))
      
      (primitive-empty() proc-types-list )

      (make-g-primitive() (proc-type (list vertices-type edges-type) graph-type))

      (primitiva-edges() (proc-type (list graph-type) edges-type))

      (primitiva-vertices() (proc-type (list graph-type) vertices-type))

      (make-l-primitive() (list (proc-type (list empty-list-type) empty-list-type)
                                (proc-type (list int-type) int-list-type)
                                (proc-type (list float-type) float-list-type)
                                (proc-type (list bool-type) bool-list-type)
                                (proc-type (list string-type) string-list-type)))

      (make-v-primitive() (list (proc-type (list int-type int-type) int-vect-type)
                                (proc-type (list int-type float-type) float-vect-type)
                                (proc-type (list int-type bool-type) bool-vect-type)
                                (proc-type (list int-type string-type) string-vect-type)
                                (proc-type (list int-type) int-vect-type)
                                (proc-type (list float-type) float-vect-type)
                                (proc-type (list bool-type) bool-vect-type)
                                (proc-type (list string-type) string-vect-type)))

      (make-d-primitive() (list (proc-type (list string-list-type generic-structure-type) generic-dict-type)
                                (proc-type (list string-list-type int-vect-type) int-dict-type)
                                (proc-type (list string-list-type float-vect-type) float-dict-type)
                                (proc-type (list string-list-type bool-vect-type) bool-dict-type)
                                (proc-type (list string-list-type string-vect-type) string-dict-type)))
      
      (primitive-list() proc-types-list)
      
      (primitive-head() (list
                         (proc-type (list int-list-type) int-type)
                         (proc-type (list float-list-type) float-type)
                         (proc-type (list bool-list-type) bool-type)
                         (proc-type (list string-list-type) string-type)))
      
      (primitive-tail() (list
                         (proc-type (list int-list-type) int-list-type)
                         (proc-type (list float-list-type) float-list-type)
                         (proc-type (list bool-list-type) bool-list-type)
                         (proc-type (list string-list-type) string-list-type)))
      
      (primitive-keys-dict()(list
                             (proc-type (list (structure-type 'dict '(string int))) string-list-type)
                             (proc-type (list (structure-type 'dict '(string float))) string-list-type)
                             (proc-type (list (structure-type 'dict '(string bool))) string-list-type)
                             (proc-type (list (structure-type 'dict '(string string))) string-list-type)))
      
      (primitive-values-dict()(list
                               (proc-type (list (structure-type 'dict '(string int))) int-vect-type)
                               (proc-type (list (structure-type 'dict '(string float))) float-vect-type)
                               (proc-type (list (structure-type 'dict '(string bool))) bool-vect-type)
                               (proc-type (list (structure-type 'dict '(string string))) string-vect-type)))

      (else "faltan tipos unarios")
      )
    )
  )

;type-of-primitive: <primitive binaria> -> <type>
;función auxiliar para determinar el tipo de una primitiva binaria
(define type-of-bin-primitive
  (lambda (prim)
    (cases primitiva-binaria prim
      (primitiva-suma () basic-aritmetic-types)
      
      (primitiva-resta () basic-aritmetic-types)
      
      (primitiva-div () basic-aritmetic-types)
      
      (primitiva-multi () basic-aritmetic-types)

      (primitiva-mod () basic-aritmetic-types)
      
      (primitiva-concat()
                       (proc-type (list string-type string-type) string-type))
      
      (primitiva-mayor() basic-logical-types)
      
      (primitiva-menor() basic-logical-types)
      
      (primitiva-mayor-igual() basic-logical-types)
      
      (primitiva-menor-igual() basic-logical-types)
      
      (primitiva-diferente() basic-logical-types)
      
      (primitiva-comparador-igual() basic-logical-types)

      (primitiva-add-edge () graph-type)
      
      (primitiva-vecinos-en() string-list-type)

      (primitiva-vecinos-sal() string-list-type)
      
      (primitiva-append ()
                        (list
                         (proc-type (list vertices-type vertices-type) vertices-type)
                         (proc-type (list edges-type edges-type) edges-type)
                         (proc-type (list empty-list-type int-list-type) int-list-type)
                         (proc-type (list empty-list-type float-list-type) float-list-type)
                         (proc-type (list empty-list-type bool-list-type) bool-list-type)
                         (proc-type (list empty-list-type string-list-type) string-list-type)
                         (proc-type (list int-list-type int-list-type) int-list-type)
                         (proc-type (list float-list-type float-list-type) float-list-type)
                         (proc-type (list bool-list-type bool-list-type) bool-list-type)
                         (proc-type (list string-list-type  string-list-type) string-list-type)))
      
      (primitiva-ref-vector ()
                            (list (proc-type (list int-vect-type int-type) int-type)
                                  (proc-type (list float-vect-type int-type) float-type)
                                  (proc-type (list bool-vect-type int-type) bool-type)
                                  (proc-type (list string-vect-type int-type) string-type))
                            )
      
      (primitiva-set-vector()
                           (list (proc-type (list int-vect-type int-type int-type) bool-type)
                                 (proc-type (list float-vect-type int-type float-type) bool-type)
                                 (proc-type (list bool-vect-type int-type bool-type) bool-type)
                                 (proc-type (list string-vect-type int-type string-type) bool-type)))
      
      (primitiva-append-vector ()
                               (list (proc-type (list int-vect-type int-type) int-vect-type)
                                     (proc-type (list float-vect-type float-type) float-vect-type)
                                     (proc-type (list bool-vect-type bool-type) bool-vect-type)
                                     (proc-type (list string-vect-type string-type) string-vect-type)))
      
      (primitiva-delete-val-pos ()
                                (list (proc-type (list int-vect-type int-type) int-vect-type)
                                      (proc-type (list float-vect-type int-type) float-vect-type)
                                      (proc-type (list bool-vect-type int-type) bool-vect-type)
                                      (proc-type (list string-vect-type int-type) string-vect-type)))
      (primitiva-ref-dict ()
                          (list
                           (proc-type (list (structure-type 'dict '(string int)) string-type) int-type)
                           (proc-type (list (structure-type 'dict '(string float)) string-type) float-type)
                           (proc-type (list (structure-type 'dict '(string bool)) string-type) bool-type)
                           (proc-type (list (structure-type 'dict '(string string)) string-type) string-type)))
      
      (primitiva-set-dict ()
                          (list
                       
                           (proc-type (list (structure-type 'dict '(string int)) string-type int-type) bool-type)
                           (proc-type (list (structure-type 'dict '(string float)) string-type float-type) bool-type)
                           (proc-type (list (structure-type 'dict '(string bool)) string-type bool-type) bool-type)
                           (proc-type (list (structure-type 'dict '(string string)) string-type string-type) bool-type)))

      (else "falta tipo binario")
      )
    )
  )


;types-of-expressions: (list-of <type-exp>) <tenv> -> (list-of <type>)
;función que mapea la función type-of-expresion a una lista
(define types-of-expressions
  (lambda (rands tenv)
    (map (lambda (exp) (type-of-expression exp tenv)) rands)))

;type-of-primitive: (list-of <symbol>) (list-of <expression>) <expression> <tenv> -> <type>
;función auxiliar para determinar el tipo de una expresión let
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

;type-of-estructure <list> -> type
;funcion que retorna el atomic type de una estructura, si todos sus elementos son
;del mismo tipo
(define type-of-structure
  (lambda (lst)
    (cond
      ((null? lst) (atomic-type 'list<empty>)) 

      ((null? (cdr lst))
       (car lst))
   
      ((equal? (car lst) (type-of-structure (cdr lst)))
       (car lst))

      (else generic-structure-type))))

;extractor para atomic-type
(define atomic-type-value
  (lambda (t)
    (cases type t
      (atomic-type (name) name)
      (else "not atomic-type"))
    )
  )

#|
Funcion que convierte el identificador de tipo de una lista de tipos
;a una expression de tipo type

NOTA: identificador de tipo se refiere a cuando escribimos
int @a = 2, int es el identificador de tipo
|#
(define eval-defined-types
  (lambda (types)
    (map expand-type-expression types)
    )
  )
;return-last-type <expression> <list-of expressions> <tenvironment>-> type 
;Funcion que ejecuta un serie de instrucciones y retorna el tipo de la ultima
;que ejecuta.
(define return-last-type
  (lambda (first-instruct instructs tenv)
    (let loop ((first-type (type-of-expression first-instruct tenv))
               (instructs instructs))
      (if (null? instructs) 
          first-type
          (loop (type-of-expression (car instructs) tenv)
                (cdr instructs)))
      )
    )
  )

;match-unary-prim-type <list-of type> <list-of type> -> type
;Funcion recibe un lista 2 listas de tipos, extrae el typo de la primera list y retorna
;con cual de los tipos de la segunda list coincide.
;NOTA: usado para las primitivas unarias
(define match-unary-prim-type
  (lambda (arg-type cases)
    (let((arg-type (if (list? arg-type)
                       (type-of-structure arg-type)
                       arg-type
                       )))
      (if (list? cases)
          (cond
            ((null? cases) (eopl:error 'match-unary-prim-type
                                       "~%Type ~s not found in ~s" arg-type cases))
      
            ((equal? arg-type (extrac-arg-type-proc (car cases)))
             (car cases))
      
            (else
             (match-unary-prim-type arg-type (cdr cases)))
            )
          cases
          )
      
      )
    )
  )


;match-binary-prim-type <type> <type> <list-of types> -> type
;Funcion que recibe 2 types y una list de proc-types y verifica si los 2 types
;coinciden con alguno de los proc-types de la list de proc-types

;NOTA:la funcion se uso principalmente para las primitivas binarias, pero por cuestiosnes de
;incluir dentro de las primitivas unarias las primitivas makes(vector,list,dict y graph)
;se uso tambien para verificar los 4 casos de las primitivas make mencionadas

(define match-binary-prim-type
  (lambda (arg-type1 arg-type2 cases)
    (if (list? cases)
        (cond
          ((null? cases)(eopl:error 'match-binary-prim-type
                                    "~%Types ~s, ~s not found in ~s"
                                    arg-type1 arg-type2 cases))
          ((and (equal? arg-type1 (car (extrac-args-types-proc (car cases))))
                (equal? arg-type2 (cadr (extrac-args-types-proc (car cases))))
                )(car cases))
          (else
           (match-binary-prim-type arg-type1 arg-type2 (cdr cases)))
          )
        cases
        )
    )
  )

;match-binary-prim-exption-type <type> <type> <type> <list-of types>
;Funcion que retorna el caso de coincidencia del tipo de las primitivas
;set-vect y set-dict

;NOTA:Esta funcion es igual a match-binary-prim-type solo que recibe un type mas,
;se realizo este ajuste, para las primitivas binarias set-vector y set-dict
;ya que estas se trabajaron asi: app-b(@miVec set-vector (1 , 2.4)) en este caso
;se usaba una lista para pasarle la posicion y el valor, por lo tanto en algunos
;casos como el de un vector de flotantes quedaba un lista con un entero(posicion) y un
;flotante(nuevo valor), lo cual no era una lista valida para la definicion del proyecto,
;la cual no aceptaba listas de valores mixtos

(define match-binary-prim-exeption-type
  (lambda (arg-type1 arg-type2 arg-type3 cases)
    (if (list? cases)
        (cond
          ((null? cases)(eopl:error 'match-binary-prim-exeption-type
                                    "~%Types ~s, ~s, ~s not found in ~s"
                                    arg-type1 arg-type2 arg-type3 cases))
          ((and (equal? arg-type1 (car (extrac-args-types-proc (car cases))))
                (equal? arg-type2 (cadr (extrac-args-types-proc (car cases))))
                (equal? arg-type3 (caddr (extrac-args-types-proc (car cases))))
                )(car cases))
          (else
           (match-binary-prim-exeption-type arg-type1 arg-type2 arg-type3 (cdr cases)))
          )
        cases
        )
    )
  )

;extrac-arg-type-proc <proc-type> -> type
;Funcion que extrae el primer typo de un proc-type
(define extrac-arg-type-proc
  (lambda (proc)
    (cases type proc
      (proc-type (args-types result-type)
                 (car args-types))
      (else (eopl:error 'extrac-args-type-proc
                        "~s No is a proc-type"
                        proc)))
    )
  )

;extrac-args-types-proc <proc-type> -> <list-of type>
;Funcion que extrae la list de types de un proc-type
(define extrac-args-types-proc
  (lambda (proc)
    (cases type proc
      (proc-type (args-types result-type)
                 args-types)
      (else (eopl:error 'extrac-args-type-proc
                        "~s No is a proc-type"
                        proc)))
    )
  )

;unary-exeption-prim?  <unary-primitive> -> string
;Funcion que retorna un string con el nombre de la primitiva unaria que tiene exepciones
;en su construccion, vector-prim y dict-prim, por el mismo motivo de las listas mistax no aceptadas
(define unary-exeption-prim?
  (lambda (un-prim)
    (cases unary-primitive un-prim
      (make-v-primitive() "vector-prim")
      (make-d-primitive() "dict-prim")
      (else "Is no a unary-exeption-prim")
      )
    )
  )
;corect-stop-cond? <type>-> bool
;Funcion que determina si la expression de la condicion de parada de un for
;es correcta, es correcta si es una expression que retorne un booleano
(define correct-stop-cond?
  (lambda (type-stop-cond)
    (cases expression type-stop-cond
      (primapp-bin-exp(e1 prim e2)
                      (cases primitiva-binaria prim
                        (primitiva-mayor()#t)
                        (primitiva-menor()#t)
                        (primitiva-mayor-igual()#t)
                        (primitiva-menor-igual()#t)
                        (primitiva-comparador-igual()#t)
                        (else #f)))
      (else #f))
    )
  )

;correct-beginning? <symbol> <expression> -> string
;Funcion que determina si la expression de inicio de un for es correcta
;es correcta si el symbol es un id y la expression es o un entero o flotante
(define correct-beginning?
  (lambda (id beginning)
    (if (and
         (is-id? id)
         (cases expression beginning
           (lit-ent-exp(n) #t)
           (lit-float-exp(n)#t)
           (else #f))
         )#t #f)
    )
  )

;correct-sumator? <expression> -> bool
;Funcion que determina si la expression de aumento del for es correcta
;es correcta si es una exprecion de seteo y la aplicacion del seteo es una
;exprecion de incremento(suma o multiplicacion) o una exprecion de decremento
;(resta)
(define correct-sumator?
  (lambda(sumator)
    (cases expression sumator
      (set-exp (id exp) (cases expression exp
                          (primapp-bin-exp (e1 prim e2)
                                           (cases primitiva-binaria prim
                                             (primitiva-suma()#t)
                                             (primitiva-resta()#t)
                                             (primitiva-multi()#t)
                                             (else #f)))
                          (else "bad value for sumator(prim)")
                          ))
      (else "bad value for sumator(set)")
      )
    )
  )

;is-id? <id> -> bool
;funcion que determina si una expression es una id
(define is-id?
  (lambda (id)
    (let* ((cadena (symbol->string id))
           (indice (caracter-index cadena)))
      (if (= indice 0) #t #f)
      )
    )
  )

;valid-option? <expression> -> bool
;Funcion que determina si la opcion a comparar en un switch es correcta
;es correcta si es ò un entero, un flotante, string
(define valid-option?
  (lambda (op)
    (cases expression op
      (lit-ent-exp(n) #t)
      (lit-float-exp(n)#t)
      (text-exp(t)#t)
      (else #f))
  )
)

;coincidence-case <scheme-value> <list-of scheme-value> <list-of expression> -> expression
;Funcion que recibe un valor y una lista de casos y retorna la expression del caso de coincidencia del valor
(define coincidence-case
  (lambda (op cases exps)
    (cond
      ((null? cases) "default")
      ((equal? op (car cases)) (car exps))
      (else (coincidence-case op (cdr cases) (cdr exps)))
      )
  )
)

#|
EJEMPLOS PARA PROBAR LAS FUNCIONES (INTERPRETADOR)
-------------------CONSTRUCCIONES------------------------------------------------------
lista inicializada------------------------make-list(1 2 3 4 5)
vector de tamaño n y valor v -------------make-vector(10 0)
vector inicializado diferentes valores----make-vector(1 2 3 4 5)
crear un diccionario----------------------make-dict(("daniel","andres")[20,29])


*********************funciones de las listas***************************

head-----------------head((1,2,3))
tail-----------------tail((1,2,3))
append---------------app-b((1,2,3) append (4,5,6))



********************funciones de vectores*****************************

ref-vector-------------------------app-b([1,2,3,4,5] ref-vector 4)
set-vector-------------------------app-b([1,2,3,4] set-vector 1 99)
append-vector----------------------app-b([1,2,3] append-vector 2 )
delete-val-vector[pos]-------------app-b([1,2,3,4,5] delete-val-pos 1)



********************funciones de diccionarios*************************

ref-dict---------app-b({"daniel":20,"andres":29} ref-dict "daniel")
keys-dict--------keys-dict({"daniel":20,"andres":29})
values-dict------values-dict({"daniel":20,"andres":29})
set-dict---------app-b({"daniel":20,"andres":29} set-dict "daniel" 99)



**********************************SUSTENTACION***************************************
*************************************************************************************

Punto (2)

GLOBALS{
int @entero = 1;
float @flotante = 2.5;
graph @grafo = make-graph(vers(@a,@b,@c) edges(edge(@a,@b) edge(@c,@b)));
string @cadena1 = "a";
string @cadena2 = "soy_una_cadena";
bool @boleano = true;
(int->int) @square = funtion(int @x)app-b(@x*@x);
list<int> @lista = make-list(1 2 3 4);
dict<string,int> @diccionario = make-dict(("daniel","andres")[20,29]);
vector<string> @vector = make-vector("hola" "soy" "un" "vector");
}PROGRAM{
  void main(){
      BLOCK{
      print(@entero)
      print(@flotante)
      print(@grafo)
      print(@cadena1)
      print(@cadena2)
      print(@boleano)
      print(@square)
      print(@lista)
      print(@diccionario)
      print(@vector)
      }}
}


punto(3)----------------------------

GLOBALS{
int @a = 0;
}PROGRAM {
  void main(){
       BLOCK{
            print(@a)
            set @a = 3
            print(@a)}
       }
}

punto(4)----------------------------
Primer Programa
GLOBALS{
int conts @a = 0;
}PROGRAM {
  int main(){
       @a
       }
}

Segundo programa
GLOBALS{
int conts @a = 0;
}PROGRAM {
  int main(){
       set @a = 3
       }
}

punto(5)----------------------------
GLOBALS{
int @sumaEnt = app-b(5 + 3);
float @sumaEntFloat = app-b(5 + 3.5);
float @sumaFloat = app-b(5.7 + 3.1);

int @restaEnt = app-b(5 ~ 3);
float @restaEntFloat = app-b(5 ~ 3.5);
float @restaFloat = app-b(5.4 ~ 3.1);

int @mulEnt = app-b(5 * 3);
float @mulEntFloat = app-b(5 * 3.5);
float @mulFloat = app-b(5.4 * 3.1);

int @divEnt = app-b(5 / 3);
float @divEntFloat = app-b(5 / 3.5);
float @divFloat = app-b(5.4 / 3.1);

int @modEnt = app-b(5 mod 3);
float @modEntFloat = app-b(5 mod 3.5);
float @modFloat = app-b(5.4 mod 3.1);

int @addEnt = add1(1);
float @addFloat = add1(1.5);

int @subEnt = sub1(1);
float @subFloat = sub1(2.3);

}PROGRAM {
  void main(){
           BLOCK{
           print(@sumaEnt)
           print(@sumaEntFloat)
           print(@sumaFloat)
           print(@restaEnt)
           print(@restaEntFloat)
           print(@restaFloat)
           print(@mulEnt)
           print(@mulEntFloat)
           print(@mulFloat)
           print(@divEnt)
           print(@divEntFloat)
           print(@divFloat)
           print(@modEnt)
           print(@modEntFloat)
           print(@modFloat)
           print(@addEnt)
           print(@addFloat)
           print(@subEnt)
           print(@subFloat)
           }
       }
}

punto(6)---------------------------------
GLOBALS{
bool @menorEnt = app-b(7 < 3);
bool @menorIgualEnt = app-b(7 <= 3);
bool @mayorEnt = app-b(7 > 3);
bool @mayotIgualEnt = app-b(7 >= 3);
bool @igualEnt = app-b(7 == 3);
bool @diferenteEnt = app-b(7 != 3);

bool @menorFloat = app-b(7.7 < 3.3);
bool @menorIgualFloat = app-b(7.4 <= 3.5);
bool @mayorFloat = app-b(7.2 > 3.8);
bool @mayotIgualFloat = app-b(7.8 >= 3);
bool @igualFloat = app-b(7.1 == 7.1);
bool @diferenteFloat = app-b(7.9 != 3.5);

bool @menorBool = app-b(true < true);
bool @menorIgualBool = app-b(false <= true);
bool @mayorBool = app-b(true > true);
bool @mayotIgualBool = app-b(false >= false);
bool @igualBool = app-b(false == true);
bool @diferenteBool = app-b(true != true);

bool @menorString = app-b("hola" < "profesor");
bool @menorIgualString = app-b("este" <= "es");
bool @mayorString = app-b("el" > "ejercicio");
bool @mayotIgualString = app-b("numero" >= "cinco");
bool @igualString = app-b("del" == "del");
bool @diferenteString = app-b("proyecto" != "final");
}PROGRAM{
   void main(){
             BLOCK{
                  print(@menorEnt)
                  print(@menorIgualEnt)
                  print(@mayorEnt)
                  print(@mayotIgualEnt)
                  print(@igualEnt)
                  print(@diferenteEnt)

                  print(@menorFloat)
                  print(@menorIgualFloat)
                  print(@mayorFloat)
                  print(@mayotIgualFloat)
                  print(@igualFloat)
                  print(@diferenteFloat)

                  print(@menorBool)
                  print(@menorIgualBool)
                  print(@mayorBool)
                  print(@mayotIgualBool)
                  print(@igualBool)
                  print(@diferenteBool)

                  print(@menorString)
                  print(@menorIgualString)
                  print(@mayorString)
                  print(@mayotIgualString)
                  print(@igualString)
                  print(@diferenteString)
             } 
        }
}
punto(7)------------------------------------------
GLOBALS{
string @cadena1 = "cadena1";
string @cadena2 = "cadena2";
}PROGRAM{
 string main(){
        Si app-b(length(app-b(@cadena1 concat @cadena2)) == 14){
        "primitivas_correctas"}sino{"primitivas_incorrectas"}
        }
}

punto(8)-------------------------------------------
PARA QUE FUNCIONE EL PROGRAMA VAYA A LA LINEA: 589 y comente
(type-of-program pgm) para desactivar
el checkeo de tipos.

void es el tipo vacio, no se usa para nada aqui, solo se puso, porque
la gramatica del global requiere un tipo.

GLOBALS{
void @fact = funtion(void @x) Si app-b(@x == 0) {1}
                                   sino {app-b(@x * app@fact(app-b(@x ~ 1)))};

void @map = funtion( void @lista , void @proc )
  Si empty?(@lista) {@lista} sino
  {app-b(make-list(app@proc(head(@lista))) append
         app@map(tail(@lista),@proc))};

void @lista = (1,2,3,4,5,6);
}PROGRAM{
  void main(){
       make-dict(("valores","factoriales")
                 make-list(make-vector(@lista) app@map(@lista,@fact)))
       }
}


punto(9)------------------------------------------

PARA QUE FUNCIONE VAYA A LA LINEA: 589 y comente (type-of-program pgm) para desactivar
el checkeo de tipos.

void es el tipo vacio, no se usa para nada aqui, solo se puso, porque
la gramatica del global requiere un tipo.

GLOBALS{
void @lista = make-list(1 2 3 4 5);
void @square = funtion(int @x) app-b(@x * @x);

void @map = funtion( void @lista , void @proc )
  Si empty?(@lista) {@lista} sino
  {app-b(make-list(app@proc(head(@lista))) append
         app@map(tail(@lista),@proc))};

}PROGRAM{
   void main(){
        app@map(@lista,@square)
        }
}

punto(10)---------------------------------------------
GLOBALS{
int @a = 1;
}PROGRAM{
    int main(){
    while(app-b(@a != 5))
    do(print(@a)
      set @a =app-b(@a + 1))
    }
}

GLOBALS{
(int->bool) @esPar? = funtion(int @x) Si app-b(app-b(@x mod 2) == 0)
{true} sino {false};
}PROGRAM{
    int main(){
    for(@a = 1;app-b(@a < 5);set @a = app-b(@a + 1))
    {
      print(app@esPar?(@a))}
    }
}

punto(11)---------------------------------------------
PARA QUE FUNCIONE VAYA A LA LINEA: 589 y comente (type-of-program pgm) para desactivar
el checkeo de tipos.

void es el tipo vacio, no se usa para nada aqui, solo se puso, porque
la gramatica del global requiere un tipo.

GLOBALS{
void @Vehiculo = funtion()
LOCALS{
void @marca = "nada";
void @modelo = "nada";
void @inicializate = funtion(void @a, void @b)
BLOCK{set @marca = @a set @modelo = @b};
void @getMarca = funtion() @marca;
void @getModelo = funtion() @modelo;
void @setMarca = funtion(void @a) set @marca = @a;
void @setModelo = funtion(void @a) set @modelo = @a;
void @dispatcher = funtion(void @op)
switch(@op){
case "inicializate": @inicializate
case "getMarca": @getMarca
case "getModelo": @getModelo
case "setMarca": @setMarca
case "setModelo": @setModelo
default: "no_method_for_class_Vehiculo"};
}{@dispatcher};

void @Moto = funtion()
LOCALS{
void @cilindrada = "nada";
void @herencia = "nada";
void @inicializate = funtion(void @a, void @b,void @c)
BLOCK{set @cilindrada = @a
set @herencia = app@Vehiculo()
app app@herencia("setMarca")(@b)
app app@herencia("setModelo")(@c)};
void @getCilindrada = funtion() @cilindrada;
void @setCilindrada = funtion(void @a) set @cilindrada = @a;
void @dispatcher = funtion(void @op)
switch(@op){
case "inicializate": @inicializate
case "getCilindrada": @getCilindrada
case "setCilindrada": @setCilindrada
case "getMarca": app@herencia("getMarca")
case "getModelo": app@herencia("getModelo")
case "setMarca": app@herencia("setMarca")
case "setModelo": app@herencia("setModelo")
default: "Method_no_found"};
}{@dispatcher};
}PROGRAM{
void main(){
 LOCALS{
void @miMoto = app@Moto();
}{
app app@miMoto("inicializate")(750,"honda","a2010")
app app@miMoto("setMarca")("kawasaki")
app app@miMoto("getMarca")()}}}

punto(12)---------------------------------------------
GLOBALS{
bool @boleano = true;
}
PROGRAM{
   bool main(){
       set @boleano = 2
       }
}

GLOBALS{
int @entero = 3;
}
PROGRAM{
   bool main(){
       set @entero = 1.7
       }
}

GLOBALS{
list<int> @listEnt = (1,2,3);
}
PROGRAM{
   bool main(){
       set @listEnt = [1,2,3]
       }
}

GLOBALS{
list<int> @listEnt = (1,2,3);
}
PROGRAM{
   bool main(){
       set @listEnt = {"daniel":20,"andres":29}
       }
}

GLOBALS{
list<int> @listEnt = (1.3,2.5,3.7);
(list<int>->int) @head = funtion(list<int> @l) head(@l);
}
PROGRAM{
   int main(){
       app@head(1)
       }
}

GLOBALS{
list<float> @listEnt = (1.3,2.5,3.7);
}
PROGRAM{
   void main(){
       Si head(@listEnt) {1} sino {2} 
       }
}

punto(13)------------------------------------
GLOBALS{
graph @graph1 = make-graph(vers(@a,@b) edges(edge(@a,@b)));
graph @graph2 = make-graph(vers(@c,@d) edges(edge(@c,@d)));
(graph*graph->graph) @unionG = funtion(graph @g1,graph @g2)
make-graph(
app-b(vertices(@g1) append vertices(@g2))
app-b(edgess(@g1) append edgess(@g2))
);
}PROGRAM{
   graph main(){
   app@unionG(@graph1,@graph2)
   }
}
|#
