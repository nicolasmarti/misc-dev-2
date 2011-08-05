(setq animals '(gazelle giraffe lion tiger))

(defun print-elements-of-list (list)
       "Print each element of LIST on a line of its own."
       (while list
         (message "%s\n" (car list))
         (setq list (cdr list))))

   
(print-elements-of-list animals)
