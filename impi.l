#
# a implish interpreter in picolisp
#
##################################################

#-- control flow ---------------------------------

(setq TRUE 'TRUE)
(setq FALSE NIL)
(setq := setq)
(setq MOD %)
(setq NOT not)

(setq BEGIN prog)
(setq THEN prog)
(setq ELSE prog)
(setq UNTIL prog)

(de PROGRAM ARGS
   (let (Name (car ARGS)
         Body (cadr ARGS))
      (set Name (list '() Body))))

(de IF ARGS
   (let (Cond (car ARGS)
         ThenBlock (cadr ARGS)
         ElseBlock (caddr ARGS) )
      (if (eval Cond)
         (eval ThenBlock)
         (eval ElseBlock) ) ) )

(de REPEAT ARGS
   (let (Block (car ARGS)
         Cond  (cadr ARGS) )
      (eval Block)
        (while (not (eval Cond))
           (eval Block) ) ) )


#-- std library ----------------------------------

(de WRITE @ (pass prin))
(de WRITELN @ (pass prinl))

#-- example program ------------------------------

(PROGRAM FizzBuzz
   (BEGIN
      (:= X 0)
      (REPEAT
         (BEGIN
            (:= X (+ X 1))
            (IF (= 0 (MOD X 15))
               (THEN (WRITE "FizzBuzz"))
               (ELSE (IF (= 0 (MOD X 3))
                        (THEN (WRITE "Fizz"))
                        (ELSE (IF (= 0 (MOD X 5))
                                 (THEN (WRITE "Buzz"))
                                 (ELSE (WRITE X)) ) ) ) ) )
            (WRITE " ") )
         (UNTIL (= X 100)) )
      (WRITELN) ) )

(de main () (FizzBuzz))
