open Lisp;;

let ctxt = init_ctxt () ;;

let _ = interp_expr ctxt"(+ 2.3 5 6 2.1)";;

let _ = interp_expr ctxt"
; this is a function
(defun add1 ((a 0)) ; this is a comment
 \"la doc\"         
 (+ a 1)   
)
";;

let _ = interp_expr ctxt"(add1 8)";;

let _ = interp_expr ctxt"(add1)";;

let _ = interp_expr ctxt"(getdoc add1)";;

let _ = interp_expr ctxt"(setq x 0)";;

let _ = interp_expr ctxt"(set 'y 0)";;

let _ = interp_expr ctxt"(let ((x 2) (y 2)) (+ x y))";;

let _ = interp_expr ctxt"x";;

let _ = interp_expr ctxt"y";;

let _ = interp_expr ctxt"(if () 'true 'false)"

let _ = interp_expr ctxt"(if t 'true 'false)"

let _ = interp_expr ctxt"(= 1 1.0)"

let _ = interp_expr ctxt"(< 1 1.0)"

let _ = interp_expr ctxt"(eq t t)"

let _ = interp_expr ctxt"(string= \"aa\" \"aa\")"

let _ = interp_expr ctxt"(string< \"aa\" \"aa\")"

let _ = interp_expr ctxt"(message \"salut doudou %s %d times !!!!!!\" 'nicolas 3.23)"

let _ = interp_expr ctxt"(cons 'doudou '(rou))"

let _ = interp_expr ctxt"(car '(doudou rou)))"

let _ = interp_expr ctxt"(cdr '(doudou rou)))"

let _ = interp_expr ctxt"(nthcdr 3 '(asd asd asd asd asd ou rou)))"

let _ = interp_expr ctxt"(nth 3 '(asd asd asd asd asd ou rou)))"

let _ = interp_exprs ctxt"
(setq x '(rou dou dou))

(setcar x 'prout)

x

(setcdr x '(rpout prout))

x
"
;;

let _ = interp_exprs ctxt"
(setq animals '(gazelle giraffe lion tiger))
     
(defun print-elements-of-list (list)
       \"Print each element of LIST on a line of its own.\"
       (while list
         (message \"%s\n\" (car list))
         (setq list (cdr list))))

(print-elements-of-list animals)

"
;;

let _ = interp_exprs ctxt"
(setq animals '(gazelle giraffe lion tiger))
     
(defun reverse-list-with-dolist (list)
    \"Using dolist, reverse the order of LIST.\"
    (let (value)  ; make sure list starts empty
      (dolist (element list value)
      (setq value (cons element value)))))
     
(reverse-list-with-dolist animals)
";;

let _ = interp_exprs ctxt"
(let (value)      ; otherwise a value is a void variable
       (dotimes (number 3 value)
         (setq value (cons number value))))
";;

let _ = interp_exprs ctxt"
(defun triangle-using-dotimes (number-of-rows)
   \"Using dotimes, add up the number of pebbles in a triangle.\"
     (let ((total 0))
       (dotimes (number number-of-rows total)
         (setq total (+ total (1+ number))))))
     
     (triangle-using-dotimes 4)
";;

let _ = interp_exprs ctxt"
(setq animals '(gazelle giraffe lion tiger))
     
     (defun print-elements-recursively (list)
       \"Print each element of LIST on a line of its own.
     Uses recursion.\"
       (when list                            ; do-again-test
             (print (car list))              ; body
             (print-elements-recursively     ; recursive call
              (cdr list))))                  ; next-step-expression
     
     (print-elements-recursively animals)
";;

let _ = interp_exprs ctxt"
(defun triangle-recursively (number)
       \"Return the sum of the numbers 1 through NUMBER inclusive.
     Uses recursion.\"
       (if (= number 1)                    ; do-again-test
           1                               ; then-part
         (+ number                         ; else-part
            (triangle-recursively          ; recursive call
             (1- number)))))               ; next-step-expression
     
     (triangle-recursively 7)
";;

let _ = interp_exprs ctxt"
(defun square-each (numbers-list)
       \"Square each of a NUMBERS LIST, recursively.\"
       (if (not numbers-list)                ; do-again-test
           nil
         (cons
          (* (car numbers-list) (car numbers-list))
          (square-each (cdr numbers-list))))) ; next-step-expression
     
     (square-each '(1 2 3))
";;


let _ = interp_exprs ctxt"
(setq animals '(gazelle giraffe lion tiger))
     
     (defun print-elements-recursively (list)
       \"Print each element of LIST on a line of its own.
     Uses recursion.\"
       (when list                            ; do-again-test
             (print (car list))              ; body
             (print-elements-recursively     ; recursive call
              (cdr list))))                  ; next-step-expression
     
     (print-elements-recursively animals)
"
;;


let _ = interp_exprs ctxt"
(defun add-elements (numbers-list)
       \"Add the elements of NUMBERS-LIST together.\"
       (if (not numbers-list)
           0
         (+ (car numbers-list) (add-elements (cdr numbers-list)))))
     
     (add-elements '(1 2 3 4))
";;

let _ = interp_exprs ctxt"
(defun keep-three-letter-words (word-list)
       \"Keep three letter words in WORD-LIST.\"
       (cond
        ;; First do-again-test: stop-condition
        ((not word-list) nil)
     
        ;; Second do-again-test: when to act
        ((eq 3 (length (symbol-name (car word-list))))
         ;; combine acted-on element with recursive call on shorter list
         (cons (car word-list) (keep-three-letter-words (cdr word-list))))
     
        ;; Third do-again-test: when to skip element;
        ;;   recursively call shorter list with next-step expression
        (t (keep-three-letter-words (cdr word-list)))))
     
     (keep-three-letter-words '(one two three four five six))
";;

let _ = interp_exprs ctxt"
(defun triangle-initialization (number)
       \"Return the sum of the numbers 1 through NUMBER inclusive.
     This is the `initialization' component of a two function
     duo that uses recursion.\"
       (triangle-recursive-helper 0 0 number))
     (defun triangle-recursive-helper (sum counter number)
       \"Return SUM, using COUNTER, through NUMBER inclusive.
     This is the `helper' component of a two function duo
     that uses recursion.\"
       (if (> counter number)
           sum
         (triangle-recursive-helper (+ sum counter)  ; sum
                                    (1+ counter)     ; counter
                                    number)))        ; number
(triangle-initialization 2)
";;

let _ = interp_exprs ctxt"
(defun silly-loop (n)
       \"Return time before and after N iterations of a loop.\"
       (let ((t1 (current-time-string)))
         (while (> (setq n (1- n))
                   0))
         (list t1 (current-time-string))))
"
let _ = interp_exprs ctxt"
 (silly-loop 500000) ; 0 sec in ocaml
";;

let _ = interp_exprs ctxt"
()
 (silly-loop 5000000) ; 7~8 sec in ocaml
";;

let _ = interp_exprs ctxt"
()
; (silly-loop 50000000) ; 10 sec on my emacs ... ~40 sec. in ocaml :((
";;


