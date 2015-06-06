; IF, LET, lt?, EQV, recursion tests

"(begin (let ((i 0) (f (lambda (x) (if (eqv? x i) 1 (* x (f (- x 1)))))) ) (define r (f 11)) ) (if (lt? r 100) 'Erro! 'Ok!) )"
"(begin (let ((a 2) (b 3)) (define x (+ a b))) (let ((x 6)) (if (eqv? x 5) (+ x 1) (- x 1) )) )"

; EQV and CONS tests

"(begin (eqv? '(1 . 2) '(3 . 4)))"
"(begin (define list1 '(a b c)) (define list2 (cons 'a '(b  c))) (eqv? list1 list2))"
"(begin (define length (lambda (lista) (if (eqv? lista '()) 0 (+ 1 (length (cdr lista)))))) (define result (length '(a b c d e))))"

; IF, SET, MOD and / Tests

"(begin (define a 6) (define b 3) (if (lt? a b) (mod a b) (/ a b 2)))"
"(begin (define a 7) (define f (lambda (x) (if (eqv? x 0) 1 (* x (f (- x 1)))))) (- (mod (f (- a 1)) a) a) )" ; -1

; QUICKSORT Test

"(begin (define concat (lambda (left pivot right) (if (eqv? left '()) (cons pivot right) (cons (car left) (concat (cdr left) pivot right))))) (define length (lambda (lista) (if (eqv? lista '()) 0 (+ 1 (length (cdr lista))) ))) (define getMenores (lambda (lista thresh) (if (eqv? lista '()) '() (if (lt? (car lista) thresh) (cons (car lista) (getMenores (cdr lista))) (getMenores (cdr lista)) )) )) (define getMaiores (lambda (lista thresh) (if (eqv? lista '()) '() (if (lt? thresh (car lista)) (cons (car lista) (getMaiores (cdr lista))) (if (eqv? thresh (car lista)) (cons (car lista) (getMaiores (cdr lista))) (getMaiores (cdr lista)) ) )) )) (define quickSort  (lambda (lista) (if (lt? (length lista) 2) lista (concat (quickSort (getMenores (cdr lista) (car lista))) (car lista) (quickSort (getMaiores (cdr lista) (car lista))))) )) (define x '(5 3 8 4 2 1 9)) (quickSort x) )"

; MAKE-CLOSURE and SET Tests

"(begin (let ((i 1)) (define f (make-closure (lambda (y) (begin (set! i (+ i y)) i) ) ) ) ) (define val1 (f 1)) (define val2 (f 2)) (+ val1 val2) )"
"(begin (let ((n 0)) (define g (make-closure (lambda (m) (begin (set! n (+ n 1)) (* m n)) ) ) ) ) (define val1 (g 4)) (define val2 (g 18)) (/ val2 val1))" ; 3
