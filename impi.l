#
# a implish interpreter in picolisp
#
##################################################

#-- helper routines for implementing the system --

# (zip '(a b c) (1 2 3))
# -> ((a . 1) (b . 2) (c . 3))
(de zip (A B)
   (if (and A B)
      (cons (cons (car A) (car B))
         (zip (cdr A) (cdr B)) ) ) )

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
# (defq) defines a function like (de), except arguments to
# the function are not evaluated.
(de defq ARGS
   (let (Name (car ARGS)
         Args (cadr ARGS)
         Body (cddr ARGS))
      (eval
         (list 'de Name 'ARGZ
            (cons 'bind
               (cons (list 'zipq Args 'ARGZ)
                  Body ) ) ) ) ) )

# For example:
# : (enlist (a b c (+ 1 2)))
# -> ((a) (b) (c) ((+ 1 2)))
(defq enlist (XS)
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
