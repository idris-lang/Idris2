; Block all reductions (e.g. needed when quoting under a 'delay')
(define ct-blockAll
  (make-thread-parameter #f))

(define (ct-isBlockAll)
  (ct-blockAll))

(define (ct-setBlockAll x)
  (ct-blockAll x))

; Check encodings of normal forms
(define (ct-isDataCon val)
  (and (vector? val) (>= (vector-ref val 0) 0)))
(define (ct-isConstant val)
  (or (number? val) (string? val) (char? val)
      (and (vector? val) (<= (vector-ref val 0) -100))))
(define (ct-isTypeCon val)
  (and (vector? val) (= (vector-ref val 0) -1)))
(define (ct-isBlocked val)
  (and (vector? val) (= (vector-ref val 0) -2)))
(define (ct-isPi val)
  (and (vector? val) (= (vector-ref val 0) -3)))
(define (ct-isTypeMatchable val)
  (or (ct-isTypeCon val) (ct-isPi val)))
(define (ct-isDelay val)
  (and (vector? val) (= (vector-ref val 0) -4)))
(define (ct-isForce val)
  (and (vector? val) (= (vector-ref val 0) -5)))
(define (ct-isErased val)
  (and (vector? val) (= (vector-ref val 0) -6)))
(define (ct-isType val)
  (and (vector? val) (= (vector-ref val 0) -7)))
(define (ct-isLambda val)
  (and (vector? val) (= (vector-ref val 0) -8)))
(define (ct-isTopLambda val)
  (and (vector? val) (= (vector-ref val 0) -9)))

; A function might be a blocked application, which is represented as
; a vector (-1, name, args), so make a new vector extending args
; (or a meta, which is a vector (-10, name, args))
(define (ct-addArg f a)
    (if (vector? f)
        (vector (vector-ref f 0) (vector-ref f 1)
             (append (vector-ref f 2) (list a)))
        (vector -11 f (list a))))

; to apply a function, either run it if it is a function, or add
; a blocked argument if it's stuck
(define (ct-app f a)
   (cond
     [(ct-isTopLambda f) ((vector-ref f 2) a)]
     [(ct-isLambda f) ((vector-ref f 1) a)]
     [(procedure? f) (f a)]
     [else (ct-addArg f a)]))

; force a delayed evaluation
(define (ct-doForce arg default)
    (if (ct-isDelay arg)
        ((vector-ref arg 4))
        default))

; primitives
(define (ct-toSignedInt x bits)
  (if (logbit? bits x)
      (logor x (ash -1 bits))
      (logand x (sub1 (ash 1 bits)))))

(define (ct-toUnsignedInt x bits)
  (logand x (sub1 (ash 1 bits))))

(define ct-u+ (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ct-toUnsignedInt (+ xval yval) bits)))))
(define ct-u- (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ct-toUnsignedInt (- xval yval) bits)))))
(define ct-u* (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ct-toUnsignedInt (* xval yval) bits)))))
(define ct-u/ (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ct-toUnsignedInt (quotient xval yval) bits)))))

(define ct-s+ (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ct-toSignedInt (+ xval yval) bits)))))
(define ct-s- (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ct-toSignedInt (- xval yval) bits)))))
(define ct-s* (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ct-toSignedInt (* xval yval) bits)))))
(define ct-s/ (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ct-toSignedInt (quotient xval yval) bits)))))

(define ct+ (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (+ xval yval)))))
(define ct- (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (- xval yval)))))
(define ct* (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (* xval yval)))))
(define ct/ (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (quotient xval yval)))))

(define ct-mod (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (remainder xval yval)))))

(define ct-neg (lambda (x)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))]
          (vector tag (- xval)))))

(define ct-bits-shl-signed (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ct-toSignedInt (shl xval yval) bits)))))
(define ct-bits-shl (lambda (x y bits)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (remainder (ash xval yval) (ash 1 bits))))))
(define ct-shl (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ash xval yval)))))

(define ct-shr (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (ash xval (- yval))))))

(define ct-and (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (logand xval yval)))))
(define ct-or (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (logor xval yval)))))
(define ct-xor (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (vector tag (logxor xval yval)))))

(define ct-string-ref (lambda (x i)
    (let [(ival (vector-ref i 1))]
         (if (and (>= ival 0) (< ival (string-length x)))
             (string-ref x ival)
             '()))))
(define ct-string-cons (lambda (x y) (string-append (string x) y)))
(define ct-string-reverse (lambda (x)
  (list->string (reverse (string->list x)))))
(define (ct-string-substr offin lenin s)
    (let* [(off (vector-ref offin 1))
           (len (vector-ref lenin 1))
           (l (string-length s))
           (b (max 0 off))
           (x (max 0 len))
           (end (min l (+ b x)))]
          (if (> b l)
              ""
              (substring s b end))))

; Don't wrap the result for bool results, we do that in Builtins.idr
(define ct< (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (< xval yval))))
(define ct<= (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (<= xval yval))))
(define ct= (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (= xval yval))))
(define ct>= (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (>= xval yval))))
(define ct> (lambda (x y)
    (let [(tag (vector-ref x 0))
          (xval (vector-ref x 1))
          (yval (vector-ref y 1))]
          (> xval yval))))

; casts
; when targetting integers, we add the Vector on the Idris side

(define ct-cast-num
  (lambda (x)
    (if (number? x) x 0)))
(define destroy-prefix
  (lambda (x)
    (cond
      ((equal? x "") "")
      ((equal? (string-ref x 0) #\#) "")
      (else x))))

(define ct-cast-string-double
  (lambda (x)
    (exact->inexact (cast-num (string->number (destroy-prefix x))))))

(define ct-cast-char-boundedInt
  (lambda (x y)
    (ct-toSignedInt (char->integer x) y)))

(define ct-cast-char-boundedUInt
  (lambda (x y)
    (ct-toUnsignedInt (char->integer x) y)))

(define ct-cast-int-char
  (lambda (xin)
    (let [(x (vector-ref xin 1))]
      (if (or
          (and (>= x 0) (<= x #xd7ff))
          (and (>= x #xe000) (<= x #x10ffff)))
        (integer->char x)
        (integer->char 0)))))

(define ct-cast-signed
  (lambda (xin bits)
    (let [(x (vector-ref xin 1))]
      (ct-toSignedInt x bits))))

(define ct-cast-unsigned
  (lambda (xin bits)
    (let [(x (vector-ref xin 1))]
      (ct-toUnsignedInt x bits))))

(define ct-cast-string-int
  (lambda (x)
    (exact-truncate (cast-num (string->number (destroy-prefix x))))))

(define ct-cast-string-boundedInt
  (lambda (x y)
    (blodwen-toSignedInt (cast-string-int x) y)))

(define ct-cast-string-boundedUInt
  (lambda (x y)
    (blodwen-toUnsignedInt (cast-string-int x) y)))

(define ct-cast-number-string
  (lambda (xin)
    (let [(x (vector-ref xin 1))]
      (number->string x))))

(define ct-exact-truncate
  (lambda (x)
    (inexact->exact (truncate x))))

(define ct-exact-truncate-boundedInt
  (lambda (x y)
    (ct-toSignedInt (exact-truncate x) y)))

(define ct-exact-truncate-boundedUInt
  (lambda (x y)
    (ct-toUnsignedInt (exact-truncate x) y)))

(define ct-int-double
  (lambda (xin)
    (let [(x (vector-ref xin 1))]
      (exact->inexact x))))
