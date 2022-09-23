;; Inspired by:
;; https://github.com/gambit/gambit/blob/master/gsc/_t-x86.scm#L1106 #L1160
(define (blodwen-os)
  (cond
    [(memq (cadr (system-type)) '(apple)) "darwin"]
    [(memq (caddr (system-type)) '(linux-gnu)) "unix"]
    [(memq (caddr (system-type)) '(mingw32 mingw64)) "windows"]
    [else "unknown"]))

;; TODO Convert to macro
(define (blodwen-read-args desc)
  (if (fx= (vector-ref desc 0) 0)
      '()
      (cons (vector-ref desc 2)
            (blodwen-read-args (vector-ref desc 3)))))

(define blodwen-lazy
  (lambda (f)
    (let ([evaluated #f] [res void])
      (lambda ()
        (if (not evaluated)
            (begin (set! evaluated #t)
                   (set! res (f))
                   (set! f void))
            (void))
        res))))

(define (blodwen-toSignedInt x bits)
  (if (bit-set? bits x)
      (bitwise-ior x (arithmetic-shift -1 bits))
      (bitwise-and x (- (arithmetic-shift 1 bits) 1))))

(define (blodwen-toUnsignedInt x bits)
  (bitwise-and x (sub1 (arithmetic-shift 1 bits))))

(define (blodwen-euclidDiv a b)
  (let ((q (quotient a b))
        (r (remainder a b)))
    (if (< r 0)
      (if (> b 0) (- q 1) (+ q 1))
      q)))

(define (blodwen-euclidMod a b)
  (let ((r (remainder a b)))
    (if (< r 0)
      (if (> b 0) (+ r b) (- r b))
      r)))

(define bu+ (lambda (x y bits) (blodwen-toUnsignedInt (+ x y) bits)))
(define bu- (lambda (x y bits) (blodwen-toUnsignedInt (- x y) bits)))
(define bu* (lambda (x y bits) (blodwen-toUnsignedInt (* x y) bits)))
(define bu/ (lambda (x y bits) (blodwen-toUnsignedInt (quotient x y) bits)))

(define bs+ (lambda (x y bits) (blodwen-toSignedInt (+ x y) bits)))
(define bs- (lambda (x y bits) (blodwen-toSignedInt (- x y) bits)))
(define bs* (lambda (x y bits) (blodwen-toSignedInt (* x y) bits)))
(define bs/ (lambda (x y bits) (blodwen-toSignedInt (blodwen-euclidDiv x y) bits)))

; To match Chez
(define (add1 x) (+ x 1))
(define (sub1 x) (- x 1))
(define (fxadd1 x) (fx+ x 1))
(define (fxsub1 x) (fx- x 1))

(define (integer->bits8 x) (bitwise-and x #xff))
(define (integer->bits16 x) (bitwise-and x #xffff))
(define (integer->bits32 x) (bitwise-and x #xffffffff))
(define (integer->bits64 x) (bitwise-and x #xffffffffffffffff))

(define (bits16->bits8 x) (bitwise-and x #xff))
(define (bits32->bits8 x) (bitwise-and x #xff))
(define (bits64->bits8 x) (bitwise-and x #xff))
(define (bits32->bits16 x) (bitwise-and x #xffff))
(define (bits64->bits16 x) (bitwise-and x #xffff))
(define (bits64->bits32 x) (bitwise-and x #xffffffff))

(define blodwen-bits-shl-signed
  (lambda (x y bits) (blodwen-toSignedInt (arithmetic-shift x y) bits)))


(define-macro (blodwen-and . args) `(bitwise-and ,@args))
(define-macro (blodwen-or . args) `(bitwise-ior ,@args))
(define-macro (blodwen-xor . args) `(bitwise-xor ,@args))
(define-macro (blodwen-bits-shl x y bits)
                   `(remainder (arithmetic-shift ,x ,y)
                               (arithmetic-shift 1 ,bits)))
(define-macro (blodwen-shl x y) `(arithmetic-shift ,x ,y))
(define-macro (blodwen-shr x y) `(arithmetic-shift ,x (- ,y)))

(define-macro (exact-floor x)
  (let ((s (gensym)))
    `(let ((,s ,x))
      (if (flonum? ,s) (##flonum->exact-int ,s) (##floor ,s)))))

(define exact-truncate
  (lambda (x)
    (inexact->exact (truncate x))))

(define exact-truncate-boundedInt
  (lambda (x y)
    (blodwen-toSignedInt (exact-truncate x) y)))

(define exact-truncate-boundedUInt
  (lambda (x y)
    (blodwen-toUnsignedInt (exact-truncate x) y)))

(define cast-char-boundedInt
  (lambda (x y)
    (blodwen-toSignedInt (char->integer x) y)))

(define cast-char-boundedUInt
  (lambda (x y)
    (blodwen-toUnsignedInt (char->integer x) y)))

(define cast-string-boundedInt
  (lambda (x y)
    (blodwen-toSignedInt (cast-string-int x) y)))

(define cast-string-boundedUInt
  (lambda (x y)
    (blodwen-toUnsignedInt (cast-string-int x) y)))

;; TODO Convert to macro
(define (cast-string-double x)
  (define (cast-num x)
    (if (number? x) x 0))
  (define (destroy-prefix x)
    (if (or (string=? x "") (char=? (string-ref x 0) #\#)) "" x))
  (exact->inexact (cast-num (string->number (destroy-prefix x)))))


(define-macro (cast-string-int x)
  `(exact-truncate (cast-string-double ,x)))

(define (from-idris-list xs)
  (if (= (vector-ref xs 0) 0)
    '()
    (cons (vector-ref xs 1) (from-idris-list (vector-ref xs 2)))))

(define-macro (string-pack xs)
  `(apply string (from-idris-list ,xs)))
(define (to-idris-list-rev acc xs)
  (if (null? xs)
    acc
    (to-idris-list-rev (vector 1 (car xs) acc) (cdr xs))))
(define (string-unpack s) (to-idris-list-rev (vector 0) (reverse (string->list s))))
(define-macro (string-concat xs)
  `(apply string-append (from-idris-list ,xs)))

(define-macro (string-cons x y)
  `(string-append (string ,x) ,y))

(define-macro (string-reverse x)
  `(list->string (reverse! (string->list ,x))))

;; TODO Convert to macro
(define (string-substr off len s)
  (let* ((start (fxmax 0 off))
         (end (fxmin (fx+ start (fxmax 0 len))
                     (string-length s))))
    (substring s start end)))

(define-macro (get-tag x) `(vector-ref ,x 0))

(define (blodwen-string-iterator-new s)
  0)

(define (blodwen-string-iterator-to-string _ s ofs f)
  (f (substring s ofs (string-length s))))

(define (blodwen-string-iterator-next s ofs)
  (if (>= ofs (string-length s))
      (vector 0)  ; EOF
      (vector 1 (string-ref s ofs) (+ ofs 1))))

;; These two are only used in this file
(define-macro (either-left x) `(vector 0 ,x))
(define-macro (either-right x) `(vector 1 ,x))

(define-macro (blodwen-error-quit msg)
  `(begin
    (display ,msg)
    (newline)
    (exit 1)))

(define (blodwen-get-line p)
  (if (input-port? p)
      (let ((str (read-line p)))
        (if (eof-object? str) "" str))
      ""))

(define (blodwen-get-char p)
  (if (input-port? p)
      (let ((chr (read-char p)))
        (if (eof-object? chr) #\nul chr))
      #\nul))

;; Threads

(define (blodwen-thread p)
  (thread-start! (make-thread (lambda () (p '#(0))))))

(define (blodwen-get-thread-data ty)
  (let ((data (thread-specific (current-thread))))
    (if (eq? data #!void) #f data)))

(define (blodwen-set-thread-data ty a)
  (thread-specific-set! (current-thread) a))

(define blodwen-mutex make-mutex)
(define blodwen-lock mutex-lock!)
(define blodwen-unlock mutex-unlock!)
(define blodwen-thisthread current-thread)

(define blodwen-condition make-condition-variable)
(define blodwen-condition-signal condition-variable-signal!)
(define blodwen-condition-broadcast condition-variable-broadcast!)
(define (blodwen-condition-wait c m)
  (mutex-unlock! m c)
  (mutex-lock! m))
(define (blodwen-condition-wait-timeout c m t) ; XXX
  (mutex-unlock! m c t)
  (mutex-lock! m))

(define blodwen-sleep thread-sleep!)
(define (blodwen-usleep s) (thread-sleep! (/ s 1e6)))


(define (blodwen-arg-count)
  (length (command-line)))

(define (blodwen-arg n)
  (if (< n (length (command-line))) (list-ref (command-line) n) ""))

(define (blodwen-hasenv var)
  (if (getenv var #f) 1 0))
