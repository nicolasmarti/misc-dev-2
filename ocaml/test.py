print Lisp.proceed("(+ 1 2 3 4)")

print Lisp.proceed("(print \"Hello World!\")")

consum, f = Lisp.proceed("(defun sillyloop (n)\
       \"Return time before and after N iterations of a loop.\" \
       (let ((t1 (current-time-string))) \
         (while (> (setq n (1- n)) \
                   0)) \
         (list t1 (current-time-string))))")

print consum
print f

print f(10)

consum, f2 = Lisp.proceed("\
(defun keepthreeletterwords (word-list)\
       \"Keep three letter words in WORD-LIST.\"\
       (cond\
        ((not word-list) nil)\
        ((eq 3 (length (symbol-name (car word-list))))\
         (cons (car word-list) (keep-three-letter-words (cdr word-list))))\
        (t (keep-three-letter-words (cdr word-list)))))")

print Lisp.sillyloop
print Lisp.keepthreeletterwords(("one", "two", "three", "four"))

