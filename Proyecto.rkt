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
<
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


;----------LEXIQUE-AND-SYNTANTIC-DEFINITIONS---------------------------
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
  '((program (expression) a-program)
    
    (expression (entero) lit-ent-exp)
    (expression (flotante) lit-float-exp)
    (expression (identifier) var-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)

    (expression ("const" type-exp identifier "=" expression ";") conts-exp)
    
    (expression 
    (unary-primitive "(" expression ")")
     primapp-un-exp)
    
    (expression
     ( "app-prim(" expression 
           primitiva-binaria expression ")")
     primapp-bin-exp)

    (expression
    (make-vector-primitive "(" (arbno expression)")")
     primapp-make-vector-exp)

    (expression (make-list-primitive "(" (arbno expression) ")")
                primapp-make-list-exp)

    (expression(make-dict-primitive "(" (arbno expression) ")")
               primapp-make-dict-exp)
    
    (expression
     ("\"" text "\"" )
    text-exp)

    (expression
     ("Si" expression "{" expression "}" "sino" "{" expression "}")
     if-exp)

    (expression
     ("declarar" "(" (arbno identifier "=" expression ";") ")"
                 "{"expression "}")
     localVar-exp)

    (expression
     ("proc" "(" (separated-list type-exp identifier ",") ")"
                   expression )
     procedure-exp)
    
    (expression
     ("eval" expression "("(separated-list expression ",")")"
              "finalEval")   
    app-exp)

    (expression
     ("letrec"
      (arbno identifier "(" (separated-list identifier ",") ")" "=" expression)
        "in" expression) 
    letrec-exp)
  
    ;PARTES DE LAS LISTAS
    (expression
     ("(" (separated-list expression ",") ")")
     list-exp)

    ;;Primitiva empty para representar una lista vacía
    (expression
     ("()")
     empty-list-exp)

    ;PARTES DE VECTORES
    (expression ("["(separated-list expression ",")"]" ) vect-exp)

    ;PARTES DE DICCIONARIOS
    (expression ("{"(separated-list  expression ":" expression ",") 
                   "}") dict-exp)

    ;PARTES DE GRAFOS
    (expression ( "edges" "(" (arbno "(" identifier "," identifier ")" ) ")") edge-exp)

    (expression ( "vertices" "(" (separated-list identifier ",") ")") vertices-exp)

    (expression ( "graph" "(" expression "," expression ")" ";") graph-exp)


    
    
    
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
    (primitiva-binaria("append") primitiva-append)
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
    (unary-primitive("empty?") primitive-empty);;----------------------------------
    (unary-primitive("list?") primitive-list)
    (unary-primitive("head") primitive-head)
    (unary-primitive("tail")primitive-tail)
    (unary-primitive("set-dict")primitive-set-dict)
    (unary-primitive("keys-dict")primitive-keys-dict)
    (unary-primitive("values-dict")primitive-values-dict)

    ;make-list-primitive
    (make-list-primitive ("make-list") make-l-primitive)
    
    (make-vector-primitive ("make-vector") make-v-primitive)
    
    (make-dict-primitive ("make-dict") make-d-primitive)
    
    ;caracteristicas adicionales
    (type-exp ("list" "<" type-exp ">") list-type-exp)
    (primitive ("zero?") zero-test-prim)    
    (type-exp ("int") int-type-exp)
    (type-exp ("float") float-type-exp)
    (type-exp ("String") String-type-exp)
    (type-exp ("bool") bool-type-exp)
    (type-exp ("(" (separated-list type-exp "*") "->" type-exp ")") proc-type-exp)
    (type-exp ("list<int>") list-int-type)
    (type-exp ("list<float>") list-float-type)
    (type-exp ("list<bool>") list-bool-type)
    (type-exp ("list<strign>") list-string-type)
    (type-exp ("vector<int>") vector-int-type)
    (type-exp ("vector<float>") vector-float-type)
    (type-exp ("vector<bool>") vector-bool-type)
    (type-exp ("vector<strign>") vector-string-type)
    
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
      (primitiva-concat () (string-append (car args) (cadr args)))
      (primitiva-mayor () (valor-verdad? (comparar (car args) (cadr args) '>)))
      (primitiva-menor () (valor-verdad? (comparar (car args) (cadr args) '<)))
      (primitiva-mayor-igual () (valor-verdad? (comparar (car args) (cadr args) '>=)))
      (primitiva-menor-igual () (valor-verdad? (comparar (car args) (cadr args) '<=)))
      (primitiva-diferente () (valor-verdad? (not (eqv? (car args) (cadr args)))))
      (primitiva-comparador-igual () (valor-verdad? (equal? (car args) (cadr args))))
      (primitiva-append() (if (not(and (list? (car args)) (list? (cadr args))))
                              (append (extract-values-list (car args))
                                      (extract-values-list (cadr args)))
                              (append (car args) (cadr args))    
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
      (primitiva-append-vector()(vector-append (car args) (cadr args)))

      (primitiva-delete-val-pos()(delete-val-pos (car args)(cadr args)))
      
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
      (primitive-neg-boolean () (if (eqv? arg "true") "false"
                                    "true"))
      (primitive-empty () (valor-verdad? (equal? (car arg) "[]")))
      
      (primitive-head ()
                      (if (list? arg)
                          (car arg)
                          (car (extract-values-list arg))
                          ))
      (primitive-tail ()
                      (if (list? arg)
                          (cdr arg)
                          (cdr (extract-values-list arg))
                          ))
      
      (primitive-keys-dict() (keys-dict arg))
      (primitive-values-dict()(values-dict arg))
      (else "faltan casos unario")
      )))


(define apply-make-l-primitive
  (lambda (prim args)
    (cases make-list-primitive prim 
      (make-l-primitive () (non-empty-list args))
    )
  )
)


(define apply-make-v-primitive
  (lambda args
    (cases make-vector-primitive (car args)
      (make-v-primitive()
                       (if (= (length args) 3)
                           (non-empty-vec (make-vector (cadr args) (caddr args)))
                           (non-empty-vec (list->vector (cdr args)))
                           )
                       )
      )   
    )
)

(define apply-make-d-primitive
  (lambda args
    (cases make-dict-primitive (car args)
       (make-d-primitive ()
               (cond
                    ((not(equal? (length args) 3)) "Not valid aplicattionfor make-dict")
                    ((and(null? (cadr args)) (null? (caddr args)))
                     (create-dict (list) (list)))
                    ((and (not(null? (cadr args)))
                          (not(null? (caddr args))))
                     (create-dict (cadr args) (caddr args))
                     )
                    )

       )
    )    
  )
)

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
    (lambda (pgm) (eval-program  pgm)) 
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
     '(@a @b @c @d @e @f)
     '(1 2 3 "hola" "FLP" (non-empty-pair 'a 'b) )
     (empty-env))))

;definición del tipo de dato ambiente
(define-datatype environment environment?
  (empty-env-record);ambiente vacio
  (extended-env-record (syms (list-of symbol?));ambiente extendido con o sin variables
                       (vals (list-of scheme-value?))
                       (env environment?))
  (recursively-extended-env-record (proc-names (list-of symbol?));ambiente extendido para la recurcion
                                   (idss (list-of (list-of symbol?)));que guarda el mismo ambiente del que extiende
                                   (bodies (list-of expression?))
                                   (env environment?)))

;definicion de scheme-value
;cualquier cosa es un scheme-value
(define scheme-value? (lambda (v) #t))

;empty-env: -> enviroment
;función que crea un ambiente vacío
(define empty-env  
  (lambda ()
    (empty-env-record)));llamado al constructor de ambiente vacío 

;extend-env: <list-of symbol> <list-of symbol> <list-of expression>
(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env))) 

;extend-env-recursively: <list-of symbols> <list-of <list-of symbols>> <list-of expressions> environment -> environment
;función que crea un ambiente extendido para procedimientos recursivos
(define extend-env-recursively
  (lambda (proc-names idss bodies old-env)
    (recursively-extended-env-record
     proc-names idss bodies old-env)))

;función que busca un símbolo en un ambiente
(define apply-env
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
                        (eopl:error 'empty-env "No binding for ~s" sym))
      (extended-env-record (syms vals old-env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env old-env sym))))
      (recursively-extended-env-record (proc-names idss bodies old-env)
                                       (let ((pos (list-find-position sym proc-names)))
                                         (if (number? pos)
                                             (closure (list-ref idss pos)
                                                      (list-ref bodies pos)
                                                      env)
                                             (apply-env old-env sym)))))))





;---------------------------AUXILIAR-FUNTIONS------------------------------------------



; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de un ambiente

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

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

#|(define conver-to-ASCII
  (lambda(palabra)
    (map char->integer (string->list palabra))
  )
)
|#

(define comparar-strings?
  (lambda (string1 string2 comparador)
    (cond
        [(equal? comparador '<) (string<? string1 string2)]
        [(equal? comparador '>) (string>? string1 string2)]
        [(equal? comparador '>=) (string>=? string1 string2)]
        [(equal? comparador '<=) (string<=? string1 string2)]
        [else (eopl:error "no se pueden comparar los strings")])))
        
(define comparar-numeros?
  (lambda (num1 num2 comparador)
    (cond
        [(equal? comparador '<) (< num1 num2)]
        [(equal? comparador '>) (> num1 num2)]
        [(equal? comparador '>=) (>= num1 num2)]
        [(equal? comparador '<=) (<= num1 num2)]
        [else (eopl:error "no se pueden comparar los numeros")])))        
    

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


;-------------------------LISTAS---------------------------------------
(define-datatype lista lista?
  (empty-list)
  (non-empty-list (values list?))
)

(define extract-values-list
  (lambda (l1)
    (cases lista l1
      (empty-list()(list))
      (non-empty-list (values) values))
  )
)

;-------------------------VECTORES---------------------------------
(define-datatype vec vec?
  (empty-vec)
  (non-empty-vec (values vector?))
)

(define extract-values-vec
  (lambda (vector)
    (cases vec vector
      (empty-vec()( #() ))
      (non-empty-vec (values) values))
  )
)

(define vector-append
  (lambda (vector value)
    (let((l1 (vector->list (extract-values-vec vector)))
         (l2 (list value)))
      (list->vector (append l1 l2))
        )
  )
)

(define delete-val-pos
  (lambda (vector pos)
    (let((delete-value (vector-ref (extract-values-vec vector) pos))
         (lista (vector->list(extract-values-vec vector))))
      (list->vector (delete-val-list lista delete-value))
        )
  )
)

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
(define-datatype dictionary dictionary?
  (empty-dict)
  (non-empty-dict (keys list)
                  (values vector?))
)

(define create-dict
  (lambda (keys values)
    (let((keys1 (extract-values-list keys))
         (values1 (extract-values-vec values))
         )
      (if (and (null? keys1) (= (vector-length values1)) 0)
        (empty-dict) 
        (non-empty-dict keys1 values1))
        )
   )
)



(define keys-dict
  (lambda (dict)
    (cases dictionary dict
      (empty-dict() "{}")
      (non-empty-dict (keys values)
                       keys)
      )
  )
)

(define values-dict
  (lambda (dict)
    (cases dictionary dict
      (empty-dict() "{}")
      (non-empty-dict (keys values)
                      values)
      )
  )
)

(define list-find-position-s
  (lambda (str los) 
    (list-index-s (lambda (str1) (string=? str1 str)) los)))

(define list-index-s
  (lambda (pred ls)
    (cond
      ((null? ls) #f)                              ; Si la lista está vacía, retorna #f
      ((pred (car ls)) 0)                          ; Si el predicado se cumple para el primer elemento, retorna 0
      (else (let ((list-index-r (list-index pred (cdr ls)))) ; Llama recursivamente para el resto de la lista
              (if (number? list-index-r) 
                  (+ list-index-r 1)                 ; Suma 1 si se encontró el índice
                  #f))))))                             ; Retorna #f si no se encontró el índice


(define ref-dict
  (lambda(dict key)    
    (let((pos (list-find-position-s key (keys-dict dict)))
         (vec-values (values-dict dict)))
      (vector-ref vec-values pos)
      )
  )
)


#|
recibe
diccionario
clave
valor a cambiar
|#

(define set-dict
  (lambda (dict values)
    (let((pos (list-find-position-s (car (extract-values-list values)) (keys-dict dict)))
         (vec-values (values-dict dict))
         )
      (vector-set! vec-values pos (cadr (extract-values-list values)))
      "cambio exitoso"
      )
    )
)
  
;----------------EXPRESSION-EVALUATOR----------------------------------



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
      (empty-list-exp () (list))
      
      (primapp-un-exp (prim rand)
                  (let ((arg (eval-expression rand env)))
                   (apply-unary-primitive prim arg)))
      
      (primapp-bin-exp (exp1 prim exp2)
                  (let ((arg1 (eval-expression exp1 env))
                        (arg2 (eval-expression exp2 env)))
                    (apply-primitive-bin prim (list arg1 arg2))))

      (primapp-make-list-exp(prim args)
                    (let((lista (eval-rands args env))  
                         )                    
                          (apply-make-l-primitive prim lista)
                      )
                    )                           
      
      
      (primapp-make-vector-exp(prim args)
                  (cond
                      ((= (length args) 2)
                      (let(
                          (size (eval-expression (car args) env))
                          (value (eval-expression (cadr args) env))
                          )
                      (apply-make-v-primitive prim size value)
                      ))                      
                      (else
                       (apply-make-v-primitive prim (eval-rands args env)))
                  )            
                  
      )

      (primapp-make-dict-exp (prim args)                                 
                         (let((keys (eval-expression (car args) env))
                              (values (eval-expression (cadr args) env)))
                           (apply-make-d-primitive prim keys values)
                             )
                             
      )
      

      (if-exp(test-exp true-exp false-exp)
             (if(true-value? (eval-expression test-exp env))
                (eval-expression true-exp env)
                (eval-expression false-exp env)))

      (localVar-exp(ids exps body)
                   (let ((args (eval-rands exps env)))
                   (eval-expression body
                                    (extend-env ids args env))))

      (procedure-exp (id-types ids body)
                     (closure ids body env))

      (app-exp (rator rands)
                 (let ((proc (eval-expression rator env))
                     (args (eval-rands rands env)))
                     (if (procval? proc)
                         (apply-procedure proc args)
                         (eopl:error 'eval-expression
                                 "Attempt to apply non-procedure ~s" proc)
                         )
                 )
               )
      (letrec-exp (proc-names ids proc-bodies letrec-body)
                  (eval-expression letrec-body
                                   (extend-env-recursively proc-names ids proc-bodies env))
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

      (else "faltan casos eval-expression")
      )    
    ))




;-----------------------------------------------------------------------------------------------
#|
EJEMPLOS PARA PROBAR LAS FUNCIONES (INTERPRETADOR)
-------------------CONSTRUCCIONES------------------------------------------------------


lista inicializada------------------------make-list(1 2 3 4 5)
vector de tamaño n y valor v -------------make-vector(10 0)
vector inicializado diferentes valores----make-vector(1 2 3 4 5)
crear un diccionario----------------------make-dict(("daniel")[20])


*********************funciones de las listas***************************

head-----------------head((1,2,3))
tail-----------------tail((1,2,3))
append---------------app-prim((1,2,3) append (4,5,6))



********************funciones de vectores*****************************

ref-vector-------------------------app-prim([1,2,3,4,5] ref-vector 4)
set-vector-------------------------app-prim([1,2,3,4] set-vector (1,99))
append-vector----------------------app-prim([1,2,3] append-vector 2 )
delete-val-vector[pos]-------------app-prim([1,2,3,4,5] delete-val-pos 1)



********************funciones de diccionarios*************************

ref-dict---------app-prim({"daniel":20,"andres":29} ref-dict "daniel")
keys-dict--------keys-dict({"daniel":20,"andres":29})
values-dict------values-dict({"daniel":20,"andres":29})
set-dict---------app-prim({"daniel":20,"andres":29} set-dict ("daniel",99))


|#