#lang eopl
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
    
    (expression 
     
    (unary-primitive "(" expression ")")
     primapp-un-exp)
    
    (expression
     ( "(" expression 
           binary-primitive expression   ")")
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

    (expression ( "list" "<"type-exp">" identifier "=" "[" (separated-list expression ",")"]"";") list-exp)

    (expression ( "vect" "<"type-exp ">" identifier "=" "("(separated-list expression ",")")"";") vect-exp)

    (expression ( "dict" "<"type-exp "," type-exp">" identifier "="
                         "{"
                         (arbno "\"" text "\"" ":" expression ",") 
                         "}"";") dict-exp)
    
    (expression ( "edges" "(" (arbno "(" identifier "," identifier ")" ) ")") edge-exp)

    (expression ( "vertices" "(" (separated-list identifier ",") ")") vertices-exp)

    (expression ( "graph" "(" expression "," expression ")" ";") graph-exp)
    
    ; binary-Primitive-exp
    (binary-primitive ("+") primitive-sum);operacion binaria para sumar
    (binary-primitive ("~") primitive-substract);operacion binaria para restar
    (binary-primitive ("*") primitive-mult);operacion binaria para multiplicar
    (binary-primitive ("/") primitive-div);operacion binaria para dividir
    (binary-primitive ("concat") primitive-con);operacion binaria para concatenar 
    (binary-primitive (">" ) primitive-greater);operacion binaria booleana para el operador logico ">"
    (binary-primitive ("<" ) primitive-minor);operacion binaria booleana para el operador logico "<"
    (binary-primitive (">=" ) primitive-greater-equal);operacion binaria booleana para el operador logico ">="
    (binary-primitive ("<=" ) primitive-minor-equal);operacion binaria booleana para el operador logico "<="
    (binary-primitive ("!=" ) primitive-diferent);operacion binaria booleana para el operador logico "!="
    (binary-primitive ("==" ) primitive-comparator-equal);operacion binaria booleana para el operador logico "=="
    
    ;unary-primitive-exp
    (unary-primitive ("length") primitive-lenght);operacion unaria para calcula longitud de un string
    (unary-primitive ("add1") primitive-add1);operacion unaria hallar el sucesor de un numero
    (unary-primitive ("sub1") primitive-sub1);operacion unaria hallar el predecesor de un numero
    (unary-primitive ("neg") primitive-neg-boolean);operacion que niega el valor de un booleano

    ;caracteristicas adicionales
    (primitive ("zero?") zero-test-prim)    
    (type-exp ("int") int-type-exp)
    (type-exp ("float") float-type-exp)
    (type-exp ("String") String-type-exp)
    (type-exp ("bool") bool-type-exp)
    (type-exp ("(" (separated-list type-exp "*") "->" type-exp ")")
              proc-type-exp)
    
    ))

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

;Funcion que resuelve las operaciones de cada primitiva unaria
;apply-unary-primitive: <primitiva> <list-of-expression> -> numero
(define apply-unary-primitive
  (lambda (prim arg)
    (cases unary-primitive prim
      (primitive-lenght () (string-length arg))
      (primitive-add1 () (+ 1 arg))
      (primitive-sub1 () (- arg 1))
      (primitive-neg-boolean () (if (eqv? arg 0) 1
                                    0))
      )))

;Funcion que resuelve las operaciones de cada primitiva binaria 
;apply-binary-primitive: <primitiva> <list-of-expression> -> numero
(define apply-binary-primitive
  (lambda (prim arg1 arg2)
    (cases binary-primitive prim
      (primitive-sum () (+ arg1 arg2))
      (primitive-substract () (- arg1 arg2))
      (primitive-mult () (* arg1 arg2))
      (primitive-div ()
                     (if (equal? arg2 0)"Division por cero"
                         (/ arg1 arg2)))
      (primitive-con () (string-append arg1 arg2))
      
      (primitive-greater () (valor-verdad? prim arg1 arg2))
      (primitive-minor () (valor-verdad? prim arg1 arg2))    
      (primitive-greater-equal () (valor-verdad? prim arg1 arg2))
      (primitive-minor-equal () (valor-verdad? prim arg1 arg2))
      (primitive-diferent () (valor-verdad? prim arg1 arg2))
      (primitive-comparator-equal () (valor-verdad? prim arg1 arg2))
      )))

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

;define-datatypes------------------------------------------------------------------
(define-datatype pareja pareja?
  (pair (first symbol?)
        (second symbol?))
)

(define pareja1 (pair 'a 'b))


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

;Funcione que retorna 1 si una operacion binaria es verdadera, o 0 si
;la exprecion es falsa
;valor_verdad?: primitiva-binaria x expression x expression => number
;usage:(valor-verdad? prim exp1 exp2) => 1 si al aplicar la primitiva a
;los 2 argumentos el valor es diferente a 0, 0 de caso contrario


(define valor-verdad?
  (lambda (prim arg1 arg2)
    (cases binary-primitive prim
      
      (primitive-greater () ())
      
      (primitive-minor () (if (< (- arg1 arg2) 0) 1
                             0))
      
      (primitive-greater-equal () (if (>= (- arg1 arg2) 0) 1
                             0))
      
      (primitive-minor-equal () (if (<= (- arg1 arg2) 0) 1
                             0))
      
      (primitive-diferent () (not(equal? arg1 arg2)))
      
      (primitive-comparator-equal () (equal? arg1 arg2))
      (else (if
             (not(equal? (apply-binary-primitive prim arg1 arg2) 0))1
             0))
    )
  )
)

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

;Funcion que retorna la concatenacion de 2 valores
;concat: a x b => String
;usage: (concat a  b) => String ab
(define concatenar
  (lambda (a b)
    (cond
      ((and (not(string? a)) (not(string? b)))
       (string-append (convert-to-string a) (convert-to-string b)))
      ((and (string? a) (not(string? b)))
       (string-append a (convert-to-string b)))
      ((and (not(string? a)) (string? b))
       (string-append (convert-to-string a) b))
      (else (string-append a b))
    )
  )
)


(define conver-to-ASCII
  (lambda(palabra)
    (map char->integer (string->list palabra))
  )
)


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
      (primapp-un-exp (prim rand)
                  (let ((arg (eval-rand rand env)))
                   (apply-unary-primitive prim arg)))
      
      (primapp-bin-exp (exp1 prim exp2)
                  (let ((arg1 (eval-rand exp1 env))
                        (arg2 (eval-rand exp2 env)))
                    (apply-binary-primitive prim arg1 arg2)))
      
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

      (else "faltan casos")
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