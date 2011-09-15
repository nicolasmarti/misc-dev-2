print Lisp.proceed("(+ 1 2 3 4)")

print Lisp.proceed("(print \"Hello World!\")")

consum, f = Lisp.proceed("(defun silly-loop (n)\
       \"Return time before and after N iterations of a loop.\" \
       (let ((t1 (current-time-string))) \
         (while (> (setq n (1- n)) \
                   0)) \
         (list t1 (current-time-string))))")

print consum
print f

print f(10)
