#
# an interpreter for implish in picolisp
#
##################################################

#-- helper routines for implementing the system --

# : (zip '(a b c) (1 2 3 4 5))
# -> ((a . 1) (b . 2) (c . 3))
(de zip (A B)
   (mapcar cons A B))

# same thing, but produce new lists instead of pairs:
# : (zipl '(a b c) (1 2 3))
# -> ((a 1) (b 2) (c 3))
(de zipl (A B)
   (zip A (mapcar list B)) )

# quoted zip. the first argument is quoted, the second evaluated
# : (zipq (a b c) (list 1 2 3))
# -> ((a . 1) (b . 2) (c . 3))
(de zipq AB
   (zip (car AB) (eval (cadr AB))))

# Now we can create quoted definitions.
# (qd) defines a function like (de), except arguments to
# the function are not evaluated.
(de qd ARGS
   # can't use bind+zipq here unless i want to use (prog) in
   # all the definition bodies. and i don't! :)
   (let (Name (car ARGS)
         Args (cadr ARGS)
         Body (cddr ARGS) )
      (def Name
         (list 'ARGZ
            (append
               (list 'bind (list 'zipq Args 'ARGZ))
               Body ) ) ) ) )

# For example:
# : (enlist (a b c (+ 1 2)))
# -> ((a) (b) (c) ((+ 1 2)))
(qd enlist (XS)
   (mapcar list XS) )

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

(qd PROGRAM (Name Body)
   (set Name (list '() Body)) )

(qd IF (Cond ThenBlock ElseBlock)
   (if (eval Cond)
      (eval ThenBlock)
      (eval ElseBlock) ) )

(qd REPEAT (Block Cond)
   (eval Block)
   (while (not (eval Cond))
      (eval Block) ) )

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
