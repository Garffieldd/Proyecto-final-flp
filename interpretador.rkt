#lang eopl
;Cesar Augusto Velasquez - 1942183
;Valery Molina Burgos- 1942630
;Andres Felipe Velasco - 1941375
;Juan Sebastian Roncancio - 1943003
;Adolfo Leon Maya - 2025159
;https://github.com/Garffieldd/Proyecto-final-flp.git

;MINI_PY

; Gramatica

;Valores denotados: Ref(Valores expresados)
;Valores expresados: enteros, flotantes, hexadecimales, cadenas de caracteres, booleanos, procedimientos, listas, registros, tuplas, objetos,

;; Definición BNF para las expresiones del lenguaje

;;  <programa>       ::= <expresion>
;;                      <un-program (exp)>

;;  <expresion>      ::= <numero>
;;                      <numero-lit (num)>
;;                   ::= "\""<texto>"\""
;;                      <texto-lit (txt)>
;;                   ::=<booleano>
;;                       <verdadero/falso> ---------------
;;                   ::= <identificador>
;;                       <identifier-exp (id)>
;;                   ::= var {<identificador>=<expresion>
;;                       } ∗ ( , ) in <expresion>
;;                   ::= const {<identificador> = <expresion>
;;                       } ∗ ( , ) in <expresion>
;;                   ::= rec {<identificador>
;;                       ( { <identificador> } ∗ ( , ) ) = <expresion>
;;                       }∗ i n <expresion>
;;                   ::= <lista>
;;                       <lista-exp (list)>
;;                   ::= crear-lista (<expresion>,<lista>|<expresion>,<crear-lista>)
;;                   ::= <tupla>
;;                       <tupla-exp (tupla)>
;;                   ::= crear-tupla (<expresion>,<tupla>|<expresion>,<crear-tupla>)
;;                   ::= <registro>
;;                       <register-exp (registro)>
;;                   ::= crear-registro {<identificador> = <expresion> , <expresion>}
;;                       <create-registro (id exp registro)>
;;                   ::= <expr-bool>
;;                   ::= x16({<numero>}*)
;;                      <numerohex-lit (lsnum)>

;;                   ::= (<expresion> <primitiva-binaria> <expresion>)
;;                      <primapp-bin-exp (exp1 prim-binaria exp2)>
;;                   ::= <primitiva-unaria> (<expresion>)
;;                      <primapp-un-exp (prim-unaria exp)>
;;                   ::= Si <expresion> entonces <expresion>  sino <expresion> finSI
;;                      <condicional-exp (test-exp true-exp false-exp)>
;;                   ::= declarar (<identificador> = <expresion> (;)) { <expresion> }
;;                      <variableLocal-exp (ids exps cuerpo)>
;;                   ::= procedimiento (<identificador>*',') haga <expresion> finProc
;;                      <procedimiento-ex (ids cuerpo)>
;;                   ::=  "evaluar" expresion   (expresion ",")*  finEval
;;                      <app-exp(exp exps)>
;;                   ::= "declarar-recursivo" (<identificador> (<identificador> ",")* "=" <expresion> ) en {<expresion>}
;;                        <letrec-exp(ids1 ids2 exp1 exp2 )>
;;                   ::= begin {<expresion>}+(;) end
;;                   ::= set <identificador> = <expresion>
;;                   ::= if <expr-bool> then <expresion> [else <expresion>] end
;;                   ::= while <expr-bool> do <expresion> done
;;                   ::= for <identificador> = <expresion> (to | downto) <expresion> do <expresion> done

;;  <identificador>::=<letter>|{<letter>|0 , . . . , 9|}∗
;;  <lista> ::= [{<expresion>} ∗ ( ; ) ]
;;          ::= vacio
;;              <lista-vacia>
;;  <tupla> ::= tupla [{<expresion>} ∗ ( ; ) ]
;;          ::= vacio
;;              <tupla-vacia>
;;  <registro> ::= { {< identificador> = <expresion> }+ (;) }
;;  <expr-bool>
;;       ::= <pred-prim>(<expresion> , <expresion>)
;;       ::= <oper-bin-bool >(<expr-bool >, <expr-bool >)
;;       ::= <bool>
;;       ::= <oper-un-bool >(<expr-bool >)
;;  <pred-prim> ::= < | > | <= | >= | == | <>
;;  <oper-bin-bool> ::= and|or
;;  <oper-un-bool> ::= not
;;  <pred-prim>         ::= < (primitiva-menor-que)
;;                      ::= > (primitiva-mayor-que)
;;                      ::= <= (primitiva-menor-o-igual-que)
;;                      ::= >= (primitiva-mayor-o-igual-que)
;;                      ::= == (primitiva-igual-que)
;;                      ::= <> (primitiva-diferente) -------------

;;  <primitiva-aritmeticas-para-hexadecimales>
;;                      ::=  +h (primitiva-suma)
;;                      ::=  -h (primitiva-resta)
;;                      ::=  *h (primitiva-multi)

;;  <primitiva-binaria> ::=  + (primitiva-suma)
;;                      ::=  - (primitiva-resta)
;;                      ::=  / (primitiva-div)
;;                      ::=  * (primitiva-multi)
;;                      ::=  % (primitiva-modulo)
;;                      ::=  concat (primitiva-concat)
;;                      ::=  append (primitiva-append)

;;  <primitiva-unaria>  ::=  longitud (primitiva-longitud)
;;                      ::=  add1 (primitiva-add1)
;;                      ::=  sub1 (primitiva-sub1)
;;                      ::=  vacio? (primitiva-vacio?)
;;                      ::=  lista? (primitiva-lista?)
;;                      ::=  tupla? (primitiva-tupla?)
;;                      ::=  cabeza (primitiva-cabeza)
;;                      ::=  cola   (primitiva-cola)
;;                      ::=  registros? (primitiva-registro)

;;  <primitiva-listas>
;;                      ::= ref-list (<lista>,<numero>) = <expresion>
;;                      ::= set-list (<lista>,<numero>,<expresion>)

;;  <primitiva-tuplas>
;;                      ::= ref-tuple (<tupla>,<numero>) = <expresion>

;;  <primitiva-registros>
;;                      ::= ref-registro(<identificador>,<registro>)
;;                      ::= set-reg ( <registro> , <numero> , <expresion>)


;******************************************************************************************

;Especificación Léxica
(define scanner-spec-simple-interpreter
  '((white-sp (whitespace) skip)
    (comment (":)" (arbno (not #\newline))) skip)
    (identificador ("@" letter (arbno (or letter digit "?"))) symbol)
    (numero (digit (arbno digit)) number)
    (numero ("-" digit (arbno digit)) number)
    (numero (digit (arbno digit) "." digit (arbno digit)) number)
    (numero ("-" digit (arbno digit) "." digit (arbno digit)) number)
    (texto ( (or letter "-") (arbno (or letter digit ":" "-"))) string))
  )

;Especificación Sintáctica (gramática)
(define grammar-simple-interpreter
  '((programa (expresion) un-programa)
    (expresion (numero) numero-lit)
    (expresion ("\"" texto "\"") texto-lit)
    (expresion (identificador) var-exp)
    (expresion (primitiva-unaria  "(" expresion ")") primapp-un-exp)
    (expresion ("Si"  expresion  "entonces" expresion "sino" expresion "finSI")
               condicional-exp)
    (expresion ("declarar" "("(separated-list identificador "=" expresion ";") ")" "{"expresion"}")
               variableLocal-exp)
    (expresion ("procedimiento" "(" (separated-list identificador ",") ")" "haga" expresion "finProc")
               procedimiento-ex)
    (expresion ("evaluar" expresion "("(separated-list expresion ",") ")" "finEval")
               app-exp)
    (expresion ("declarar-recursivo" "("(arbno identificador "(" (separated-list identificador ",") ")" "=" expresion) ")" "en" "{"expresion"}") 
               letrec-exp)
    (expresion
     ;Recordar: Definición de terminal para primapp-exp
     ("(" expresion primitiva-binaria expresion ")")
     primapp-bin-exp)
    
    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("~") primitiva-resta)
    (primitiva-binaria ("/")primitiva-div)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("concat") primitiva-concat)
    (primitiva-unaria ("longitud") primitiva-longitud)
    (primitiva-unaria ("add1") primitiva-add1)
    (primitiva-unaria ("sub1") primitiva-sub1)
    )
  )

;Construidos automáticamente:

(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)))

;*******************************************************************************************
;Parser, Scanner, Interfaz

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Analizador Léxico (Scanner)

(define just-scan
  (sllgen:make-string-scanner scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Interpretador (FrontEnd + Evaluación + señal para lectura )

(define interpretador
  (sllgen:make-rep-loop  "(͡° ͜ʖ͡°) "
                         (lambda (pgm) (evaluar-programa  pgm)) 
                         (sllgen:make-stream-parser 
                          scanner-spec-simple-interpreter
                          grammar-simple-interpreter)))

;*******************************************************************************************
;El Interprete

;evaluar-programa: <programa> -> numero
; función que evalúa un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)

(define evaluar-programa
  (lambda (pgm)
    (cases programa pgm
      (un-programa (body)
                   (evaluar-expresion body (ambiente-inicial))))))

; Ambiente inicial
;(define ambiente-inicial
;  (lambda ()
;    (extender-ambiente
;     '(@a @b @c @d @e)
;     '(1 2 3 "hola" "FLP")
;     (empty-env))))

(define ambiente-inicial
  (lambda ()
    (extender-ambiente
     '(@a @b @c @d @e)
     '(1 2 3 "hola" "FLP")
     (empty-env))))

;evaluar-expresion: <expresion> <enviroment> -> numero
; evalua la expresión en el ambiente de entrada
(define evaluar-expresion
  (lambda (exp env)
    (cases expresion exp
      (numero-lit (num) num)
      (texto-lit (txt) txt)
      (var-exp (id) (buscar-variable env id))
      (primapp-bin-exp (rand1 prim rand2)
                       (aplicar-primitiva-binaria prim (evaluar-rand rand1 env) (evaluar-rand rand2 env)))
      (primapp-un-exp (prim rand)
                      (aplicar-primitiva-unaria prim (evaluar-rand rand env))
                      )
      (condicional-exp (test-exp true-exp false-exp)
                       (if (valor-verdad? (evaluar-expresion test-exp env))
                           (evaluar-expresion true-exp env)
                           (evaluar-expresion false-exp env)))
      (variableLocal-exp (ids rands body)
                         (let ((args (evaluar-rands rands env)))
                           (evaluar-expresion body
                                              (extender-ambiente ids args env))))
      (procedimiento-ex (ids body)
                        (closure ids body env))
      (app-exp (rator rands)
               (let ((proc (evaluar-expresion rator env))
                     (args (evaluar-rands rands env)))
                 (if (procval? proc)
                     (aplicar-procedimiento proc args)
                     (eopl:error 'evaluar-expresion
                                 "Intento de aplicar el no procedimiento ~s" proc))))
      (letrec-exp (proc-names idss bodies letrec-body)
                  (evaluar-expresion letrec-body
                                     (extender-ambiente-recursivamente proc-names idss bodies env))))))

; funciones auxiliares para aplicar evaluar-expresion a cada elemento de una 
; lista de operandos (expresiones)

(define evaluar-rands
  (lambda (rands env)
    (map (lambda (x) (evaluar-rand x env)) rands)))

(define evaluar-rand
  (lambda (rand env)
    (evaluar-expresion rand env)))

;aplicar-primitiva-binaria: <expresion> <primitiva> <expresion> -> numero o string dependiendo de la primitiva 
(define aplicar-primitiva-binaria
  (lambda (prim rand1 rand2)
    (cases primitiva-binaria prim
      (primitiva-suma () (+ rand1 rand2))
      (primitiva-resta () (- rand1 rand2))
      (primitiva-div () (/ rand1 rand2))
      (primitiva-multi () (* rand1 rand2))
      (primitiva-concat () (concat rand1 rand2))
      )
    )
  )

;aplicar-primitiva-unaria: <primitiva> <expresion>  -> numero
(define aplicar-primitiva-unaria
  (lambda (prim rand)
    (cases primitiva-unaria prim
      (primitiva-add1 () (+ rand 1))
      (primitiva-sub1 () (- rand 1))
      (primitiva-longitud () (if (string? rand) (string-length rand) (length rand)))
      )
    )
  )

;valor-verdad?: determina si un valor dado corresponde a un valor booleano falso (0) o verdadero (diferente a 0)
(define valor-verdad?
  (lambda (x)
    (not (zero? x))))
;*******************************************************************************************
;Procedimientos
(define-datatype procval procval?
  (closure
   (ids (list-of symbol?))
   (body expresion?)
   (env environment?)))

;aplicar-procedimiento: evalua el cuerpo de un procedimientos en el ambiente extendido correspondiente
(define aplicar-procedimiento
  (lambda (proc args)
    (cases procval proc
      (closure (ids body env)
               (evaluar-expresion body (extender-ambiente ids args env))))))

;*******************************************************************************************
;Ambientes

;definición del tipo de dato ambiente
(define-datatype environment environment?
  (vacio)
  (registro-ambiente-extendido (syms (list-of symbol?))
                               (vals (list-of scheme-value?))
                               (env environment?))
  (registro-ambiente-extendido-recursivamente (proc-names (list-of symbol?))
                                              (idss (list-of (list-of symbol?)))
                                              (bodies (list-of expresion?))
                                              (env environment?)))

(define scheme-value? (lambda (v) #t))

;empty-env:      -> enviroment
;función que crea un ambiente vacío
(define empty-env  
  (lambda ()
    (vacio)))       ;llamado al constructor de ambiente vacío 


;extender-ambiente: <list-of symbols> <list-of numbers> enviroment -> enviroment
;función que crea un ambiente extendido
(define extender-ambiente
  (lambda (syms vals env)
    (registro-ambiente-extendido syms vals env)))

;extender-ambiente-recursivamente: <list-of symbols> <list-of <list-of symbols>> <list-of expressions> environment -> environment
;función que crea un ambiente extendido para procedimientos recursivos
(define extender-ambiente-recursivamente
  (lambda (proc-names idss bodies old-env)
    (registro-ambiente-extendido-recursivamente
     proc-names idss bodies old-env)))

;función que busca un símbolo en un ambiente
(define buscar-variable
  (lambda (env sym)
    (cases environment env
      (vacio ()
             (eopl:error 'empty-env "No binding for ~s" sym))
      (registro-ambiente-extendido (syms vals old-env)
                                   (let ((pos (list-find-position sym syms)))
                                     (if (number? pos)
                                         (list-ref vals pos)
                                         (buscar-variable old-env sym))))
      (registro-ambiente-extendido-recursivamente (proc-names idss bodies old-env)
                                                  (let ((pos (list-find-position sym proc-names)))
                                                    (if (number? pos)
                                                        (closure (list-ref idss pos)
                                                                 (list-ref bodies pos)
                                                                 env)
                                                        (buscar-variable old-env sym)))))))

;****************************************************************************************
;Funciones Auxiliares

; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de unambiente

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

;funcion auxiliar que concatena 2 expresiones (solo texto)
(define concat
  (lambda (s1 s2)
    (if (and (string? s1) (string? s2))
        (string-append s1  s2)
        (eopl:error " Solo se pueden concatenar Strings:"))))



