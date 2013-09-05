#
# a implish interpreter in picolisp
#
##################################################

#-- the language ---------------------------------

(de repeat ARGS
   (let (Block (car ARGS) Cond  (cadr ARGS))
      (eval Block)
        (while (not (eval Cond))
           (eval Block) ) ) )

#-- std library ----------------------------------

(de write @ (pass prin))
(de writeln @ (pass prinl))

#-- example program ------------------------------

(de main ()
   (setq X 0)
   (repeat
      (prog (setq X (inc X))
         (write X " ") )
      (= X 10) )
   (writeln))
