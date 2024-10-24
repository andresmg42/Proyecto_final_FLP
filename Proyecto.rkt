#lang eopl
(require racket/format)


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
  '((program (expression) a-program)
    
    (expression (entero) lit-ent-exp)
    (expression (flotante) lit-float-exp)
    (expression (identifier) var-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)

    (expression ("const" type-exp identifier "=" expression ";") conts-exp)
    
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
    (expression ("(" (separated-list expression ",") ")") list-exp)

    (expression ("["  (separated-list expression ",") "]") vec-exp)

   
   

    ;(expression (unary-primitive "(" (arbno expression) ")") data-structure-exp)

    

    ;; Primitiva empty para representar una lista vacía
    (expression ("()") empty-list-exp)

    (expression ("[]") empty-vec-exp)
    
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
    (primitiva-binaria ("append-list") primitiva-append-list)
  

    
    ;unary-primitive-exp
    (unary-primitive ("length") primitive-lenght);operacion unaria para calcula longitud de un string
    (unary-primitive ("add1") primitive-add1);operacion unaria hallar el sucesor de un numero
    (unary-primitive ("sub1") primitive-sub1);operacion unaria hallar el predecesor de un numero
    (unary-primitive ("neg") primitive-neg-boolean);operacion que niega el valor de un booleano
    (unary-primitive("empty?") primitive-empty);;----------------------------------
    (unary-primitive("list?") primitive-list);;falta
    (unary-primitive("head") primitive-head)
    (unary-primitive("tail")primitive-tail)
    (unary-primitive ("make-list") primitive-make-list)
    (unary-primitive ("make-vec") primitive-make-vec)
    (unary-primitive ("make-vec-zise") primitive-make-vec-zise)
    (unary-primitive ("ref-vector") primitive-ref-vector)
    (unary-primitive ("set-vector") primitive-set-vector)
    (unary-primitive ("append-vector") primitive-append-vector)
    (unary-primitive ("delete-val-vector") primitive-delete-vec)
    
    

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
    
    
    ))

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
      (primitiva-append-list () (append-list args))
    
       (else "faltan casos bianrio")
 
      
      
                       
      )))

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
      (primitive-empty () (valor-verdad? (equal? (car arg) "[]")))
      (primitive-head () (car arg))
      (primitive-tail () (cdr arg))
      ;;falta primitive list?
      ;;falta vector?
      (primitive-make-list () (make-struct arg 'list))
      (primitive-make-vec () (make-struct arg 'vector))
      (primitive-make-vec-zise () (make-vec-zise arg))
      (primitive-ref-vector () (vector-ref (car arg) (cadr arg)))
      (primitive-set-vector () (let (
                                     ( v (vector-set! (car arg) (cadr arg) (caddr arg)))
                                     )
                                      (make-struct (vector->list (car arg)) 'vector)
                                     ))
      (primitive-append-vector () (let(

                                       (l (append (vector->list (car arg)) (cdr arg)))


                                       )(make-struct l 'vector)))
      (primitive-delete-vec () (let(
                                   (l (eliminar-pos (vector->list (car arg)) (cadr arg) 0))

                                    )
                                 (make-struct l 'vector)))
                                    
                                                    
      (else "faltan casos unario")
      )))


 (define eliminar-pos
   (lambda (arg pos acc)
     (if (null? arg) '()
         (cond
           [(not (equal? acc pos)) (cons (car arg) (eliminar-pos (cdr arg) pos (+ acc 1)))]
           [(and (equal? acc pos) (not (null? (cdr arg)))) (cons (cadr arg) (eliminar-pos (cddr arg) pos (+ acc 2)))]
           [else '()]
           ))))
         
     


;Funcione que retorna 1 si una operacion binaria es verdadera, o 0 si
;la exprecion es falsa
;valor_verdad?: primitiva-binaria x expression x expression => number
;usage:(valor-verdad? prim exp1 exp2) => 1 si al aplicar la primitiva a
;los 2 argumentos el valor es diferente a 0, 0 de caso contrario


(define valor-verdad?
  (lambda (bool)
    (if bool "true" "false")))


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

;eval-program: <programa> -> numero
;función que evalúa un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)
(define eval-program
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
                 (eval-expression body (init-env))))))

;ambiente inicial
(define init-env
  (lambda ()
    (extend-env
     '(@a @b @c @d @e @f)
     '(1 2 3 "hola" "FLP" (non-empty-pair 'a 'b) )
     (empty-env))))


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
               (eval-expression body (extend-env ids args env))))))

;Funcion que define los valores de verdad, 0 = false y diferente de 0 = true
;true-value?: numero -> boolean
(define true-value?
  (lambda (x)
    (not (zero? x))))


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


;extend-env-recursively: <list-of symbols> <list-of <list-of symbols>> <list-of expressions> environment -> environment
;función que crea un ambiente extendido para procedimientos recursivos
(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env))) 

;extend-env: <list-of symbol> <list-of symbol> <list-of expression>
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


;-------------------------------------------------------------------------------------------
;Funciones Auxiliares

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


        
         
(define make-struct
  (lambda (arg type)
    (letrec(
         
     (make (lambda (arg)
        (if (null? arg) ""
            (if (null? (cdr arg))
                (string-append (~a (car arg)) (make (cdr arg)))
                (string-append (~a (car arg)) "," (make (cdr arg)))

            ))))
     )
    (cond
      [(or (equal? (car arg) "()") (equal? (car arg) "[]")) (car arg)]
      [(equal? type 'list) (string-append "("(make arg) ")")]
      [(equal? type 'vector) (string-append "["(make arg) "]")]
      [(equal? type 'append) (make arg)]
      
        


    ))))

 (define make-vec-zise
   (lambda (arg)
     (letrec(
           (tamaño (if (null? arg) 0 (car arg)))
          (relleno (if (null? arg) "" (~a (cadr arg))))
          
          (crear
           (lambda(tamaño relleno)
             (if (equal? tamaño 0) ""
                 (if (equal? (- tamaño 1) 0)
                 (string-append relleno (crear (- tamaño 1) relleno))
                 (string-append relleno "," (crear (- tamaño 1) relleno))
                 ))))
          )
          (string-append "[" (crear tamaño relleno) "]")
       )))
  
                 
(define append-list
  (lambda (arg)
    (let(
         (list1 (if (equal? (car arg) "()") "" (make-struct (car arg) 'append)))
         (list2 (if (equal? (cadr arg) "()") "" (make-struct (cadr arg) 'append)))
         )
      (if(or (equal? list1 "") (equal? list2 ""))
       (string-append "(" list1  list2 ")") 
       (string-append "(" list1 "," list2 ")")
       ))))
                 
          




    

;eval-expression: <expression> <enviroment> -> numero
; evalua la expresión en el ambiente de entrada
(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (lit-ent-exp (datum) datum)
      (lit-float-exp (datum) datum)
      (var-exp (id) (apply-env env id))
      (text-exp (text) text)
      (true-exp () "true")
      (false-exp () "false")
      (empty-list-exp () "()")
      (empty-vec-exp () "[]")
      ;;primap-exp
      (primapp-un-exp (prim rand)
                  (let ((arg (eval-rands rand env)))
                   (apply-unary-primitive prim arg)))
      
      (primapp-bin-exp (exp1 prim exp2)
                  (let ((arg1 (eval-expression exp1 env))
                        (arg2 (eval-expression exp2 env)))
                    (apply-primitive-bin prim (list arg1 arg2))))
      
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
      ;;faltan algunos cambios----------------------------
      (list-exp (args)
                (eval-rands args env))
      (vec-exp (args) (list->vector (eval-rands args env)))
              
                     

      (else 'error)
      )    
    ))

;-----------------------------------------------------------------------------------------------
#|
PUNTOS DEL TALLER
a) sumarDigitos

La funcion @modulo calcula el resto de divir un numero entre otro
@modulo: number x number => number
usage: eval @modulo(@a,@b) finalEval => residuo de dividir @a entre @b

La funcion @divEntera calcula la division entera entre 2 numero
@divEnt: number x number => number
usage: eval @divEntera(@a,@b) finalEval => resultado entero de divir @a entre @b

La funcion @sumarDigitos suma los digitos de una numero dado
@sumarDigitos: number => number
usage: eval @sumarDititos(@a) finalEval => resultado de sumar lo digitos de @a

letrec @modulo(@n,@m)= Si (@n<@m) {@n} sino {eval @modulo((@n~@m),@m) finalEval}
@divEntera(@t,@r)= ((@t/@r) ~ (eval @modulo (@t,@r) finalEval / @r))
@sumarDigitos(@h)= Si (@h==0) {0} sino 
{(eval @modulo (@h,10) finalEval + eval@sumarDigitos(eval @divEntera (@h,10) finalEval) finalEval)}
in
eval @sumarDigitos (147) finalEval
----------------------------------------------------------------------------------------
b)
Funcion que retorna el factorial de un numero n
@fact: number => number
usage: eval @fact(@n) finalEval => factorial de @n

Factorial de 5
letrec
@fact(@x)= Si (@x == 0) {1} sino {(@x * eval @fact((@x ~ 1)) finalEval)}
in
eval @fact(5) finalEval


Factorial de 10

letrec
@fact(@x)= Si (@x == 0) {1} sino {(@x * eval @fact((@x ~ 1)) finalEval)}
in
eval @fact(10) finalEval

----------------------------------------------------------------------------------------
c) Potencia

Funcion que calcula la potencia de un numero a elevado a la potencia b
@potencia: number x number => number
usage: eval @potencia(@a,@b) finalEval => a elevado a la b

letrec
@potencia(@a,@b) = Si (@b == 1) {@a} sino
                      {Si (@b == 0) {1} sino
                           {(@a * eval @potencia(@a,(@b ~ 1)) finalEval)}} 
in
eval @potencia(4,2) finalEval
-----------------------------------------------------------------------------------------
d) SumarRango

Funcion que retorna la suma de los numeros en un rango positivo
@sumRan: number x number => number
usage: eval @sumRan(@a,@b) => suma de los numeros desde @a hasta @b

letrec
@sumRan(@a,@b) = Si (@a == @b) {@a} sino {(@a + eval @sumRan((@a + 1),@b) finalEval)}
in
eval @sumRan(2,5) finalEval

-----------------------------------------------------------------------------------------
e) Decorators

Funcion decoradora que retorna hola al inicio de un string
@saludar: procedure => String
usage: eval @decorate() finalEval => "hola:Algun_string"

declarar(
@integrantes = procedure(){"Andres_Y_Daniel"};
@saludar = procedure(@noms){procedure(){("Hola: " concat eval @noms() finalEval)}};
){
declarar(@decorate = eval @saludar(@integrantes) finalEval;)
{eval @decorate()  finalEval}}



f)
Funcion decoradora que recibe un string y lo agregar al final del otro string
@decorate: string => string
usage: @decorate(mensaje) => "algun_stringmensaje"

declarar(
@integrantes = procedure(){"Andres_Y_Daniel"};
@saludar = procedure(@noms){procedure(){("Hola: " concat eval @noms() finalEval)}};
){
declarar(@evaluado = eval @saludar(@integrantes) finalEval;)
{
declarar(@decorate = procedure(@mensaje){
(eval @evaluado() finalEval concat @mensaje)};)
{eval @decorate("Estudiantes_de_FLP") finalEval}}}
|#