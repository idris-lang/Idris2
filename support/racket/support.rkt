(define (blodwen-os)
  (case (system-type 'os)
    [(unix) "unix"]
    [(macosx) "darwin"]
    [(windows) "windows"]
    [else "unknown"]))

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
  (if (bitwise-bit-set? x bits)
      (bitwise-ior x (arithmetic-shift (- 1) bits))
      (bitwise-and x (sub1 (arithmetic-shift 1 bits)))))

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
(define (fxadd1 x) (unsafe-fx+ x 1))
(define (fxsub1 x) (unsafe-fx- x 1))

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

(define blodwen-bits-shl (lambda (x y bits) (remainder (arithmetic-shift x y) (arithmetic-shift 1 bits))))
(define blodwen-shl (lambda (x y) (arithmetic-shift x y)))
(define blodwen-shr (lambda (x y) (arithmetic-shift x (- y))))
(define blodwen-and (lambda (x y) (bitwise-and x y)))
(define blodwen-or (lambda (x y) (bitwise-ior x y)))
(define blodwen-xor (lambda (x y) (bitwise-xor x y)))

(define exact-floor
  (lambda (x)
    (inexact->exact (floor x))))

(define blodwen-bits-shl-signed
  (lambda (x y bits) (blodwen-toSignedInt (arithmetic-shift x y) bits)))

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

(define cast-string-int
  (lambda (x)
    (exact-truncate (cast-num (string->number (destroy-prefix x))))))

(define cast-string-boundedInt
  (lambda (x y)
    (blodwen-toSignedInt (cast-string-int x) y)))

(define cast-string-boundedUInt
  (lambda (x y)
    (blodwen-toUnsignedInt (cast-string-int x) y)))

(define cast-num
  (lambda (x)
    (if (number? x) x 0)))
(define destroy-prefix
  (lambda (x)
    (cond
      ((equal? x "") "")
      ((equal? (string-ref x 0) #\#) "")
      (else x))))

(define cast-int-char
  (lambda (x)
    (if (or
          (and (>= x 0) (<= x #xd7ff))
          (and (>= x #xe000) (<= x #x10ffff)))
        (integer->char x)
        (integer->char 0))))

(define cast-string-double
  (lambda (x)
    (exact->inexact (cast-num (string->number (destroy-prefix x))))))
(define (string-concat xs) (apply string-append xs))
(define (string-unpack s) (string->list s))
(define (string-pack xs) (list->string xs))
(define string-cons (lambda (x y) (string-append (string x) y)))
(define string-reverse (lambda (x)
  (list->string (reverse (string->list x)))))
(define (string-substr off len s)
    (let* ((l (string-length s))
          (b (max 0 off))
          (x (max 0 len))
          (end (min l (+ b x))))
          (substring s b end)))

(define (blodwen-string-iterator-new s)
  0)

(define (blodwen-string-iterator-to-string _ s ofs f)
  (f (substring s ofs (string-length s))))

(define (blodwen-string-iterator-next s ofs)
  (if (>= ofs (string-length s))
      '() ; EOF
      (cons (string-ref s ofs) (+ ofs 1))))

(define either-left
  (lambda (x)
    (vector 0 x)))

(define either-right
  (lambda (x)
    (vector 1 x)))

(define blodwen-error-quit
  (lambda (msg)
    (display msg)
    (newline)
    (exit 1)))

(define (blodwen-get-line p)
    (if (port? p)
        (let ((str (read-line p)))
            (if (eof-object? str)
                ""
                str))
        (void)))

(define (blodwen-get-char p)
    (if (port? p)
        (let ((chr (read-char p)))
            (if (eof-object? chr)
                #\nul
                chr))
        (void)))

;; Buffers

(define (blodwen-new-buffer size)
  (make-bytevector size 0))

(define (blodwen-buffer-size buf)
  (bytevector-length buf))

(define (blodwen-buffer-setbyte buf loc val)
  (bytevector-u8-set! buf loc val))

(define (blodwen-buffer-getbyte buf loc)
  (bytevector-u8-ref buf loc))

(define (blodwen-buffer-setbits16 buf loc val)
  (bytevector-u16-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getbits16 buf loc)
  (bytevector-u16-ref buf loc (native-endianness)))

(define (blodwen-buffer-setbits32 buf loc val)
  (bytevector-u32-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getbits32 buf loc)
  (bytevector-u32-ref buf loc (native-endianness)))

(define (blodwen-buffer-setbits64 buf loc val)
  (bytevector-u64-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getbits64 buf loc)
  (bytevector-u64-ref buf loc (native-endianness)))

(define (blodwen-buffer-setint32 buf loc val)
  (bytevector-s32-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getint32 buf loc)
  (bytevector-s32-ref buf loc (native-endianness)))

(define (blodwen-buffer-setint buf loc val)
  (bytevector-s64-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getint buf loc)
  (bytevector-s64-ref buf loc (native-endianness)))

(define (blodwen-buffer-setdouble buf loc val)
  (bytevector-ieee-double-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getdouble buf loc)
  (bytevector-ieee-double-ref buf loc (native-endianness)))

(define (blodwen-stringbytelen str)
  (bytevector-length (string->utf8 str)))

(define (blodwen-buffer-setstring buf loc val)
  (let* [(strvec (string->utf8 val))
         (len (bytevector-length strvec))]
    (bytevector-copy! strvec 0 buf loc len)))

(define (blodwen-buffer-getstring buf loc len)
  (let [(newvec (make-bytevector len))]
    (bytevector-copy! buf loc newvec 0 len)
    (utf8->string newvec)))

(define (blodwen-buffer-copydata buf start len dest loc)
  (bytevector-copy! buf start dest loc len))

;; Threads

;; NB: Racket threads are green/virtual threads meaning extra caution is to be
;; taken when using FFI functions in combination with threads. The *entire*
;; Racket runtime blocks on a foreign call, meaning no threads will progress
;; until the foreign call returns.

(define (blodwen-thread proc)
  (thread (lambda () (proc (vector 0)))))

(define (blodwen-thread-wait handle)
  (thread-wait handle))

;; Thread mailboxes

(define blodwen-thread-data (make-thread-cell #f))

(define (blodwen-get-thread-data ty)
  (thread-cell-ref blodwen-thread-data))

(define (blodwen-set-thread-data ty a)
  (thread-cell-set! blodwen-thread-data a))

;; Semaphores

(define (blodwen-make-semaphore init)
  (make-semaphore init))

(define (blodwen-semaphore-post sema)
  (semaphore-post sema))

(define (blodwen-semaphore-wait sema)
  (semaphore-wait sema))

;; Barriers

(struct barrier (count-box num-threads mutex semaphore))

(define (blodwen-make-barrier num-threads)
  (barrier (box 0) num-threads (blodwen-make-mutex) (make-semaphore 0)))

(define (blodwen-barrier-wait barrier)
  (blodwen-mutex-acquire (barrier-mutex barrier))
  (let* [(count-box (barrier-count-box barrier))
         (count-old (unbox count-box))
         (count-new (+ count-old 1))
         (sema (barrier-semaphore barrier))]
    (set-box! count-box count-new)
    (blodwen-mutex-release (barrier-mutex barrier))
    (when (= count-new (barrier-num-threads barrier)) (semaphore-post sema))
    (semaphore-wait sema)
    (semaphore-post sema)
    ))

;; Channels

(define (blodwen-make-channel ty)
  (make-async-channel 1))

(define (blodwen-channel-get ty chan)
  (async-channel-get chan))

(define (blodwen-channel-put ty chan val)
  (async-channel-put chan val))

;; Mutex

(define (blodwen-make-mutex)
  (make-semaphore 1))

(define (blodwen-mutex-acquire sema)
  (semaphore-wait sema))

(define (blodwen-mutex-release sema)
  (if (semaphore-try-wait? sema)
      (blodwen-error-quit "Exception in mutexRelease: thread does not own mutex")
      (semaphore-post sema)))

;; Condition Variables
;; As per p.5 of the MS paper
;; https://www.microsoft.com/en-us/research/wp-content/uploads/2004/12/ImplementingCVs.pdf

; The MS paper has the mutex be part of the CV, but that seems to be contrary to
; most other implementations
(struct cv (countingSem waitersLock waiters handshakeSem) #:mutable)

; CONSTRUCTOR
(define (blodwen-make-cv)
  (let ([s (make-semaphore 0)]
        [x (make-semaphore 1)]
        [h (make-semaphore 0)])
    (cv s x 0 h)))

;; MS paper: sem.V() := sem-post  /* "sem.V() increments sem.count, atomically" */
;;           sem.P() := sem-wait
;; (turns out this is Dijkstra's fault: P and V match up with the Dutch
;;  terminology)

; WAIT
(define (blodwen-cv-wait my-cv m)
    ; atomically increment waiters
    (semaphore-wait (cv-waitersLock my-cv))
    (set-cv-waiters! my-cv (+ (cv-waiters my-cv) 1))
    (semaphore-post (cv-waitersLock my-cv))
    ; release the provided mutex
    (blodwen-mutex-release m)
    ; wait for the counting semaphore to let us through
    (semaphore-wait (cv-countingSem my-cv))
    ; signal to broadcast that we have proceeded past the critical point/have
    ; been woken up successfully
    (semaphore-post (cv-handshakeSem my-cv))
    ; re-acquire the provided mutex
    (blodwen-mutex-acquire m)
    )

; SIGNAL
(define (blodwen-cv-signal my-cv)
    ; lock access to waiters
    (semaphore-wait (cv-waitersLock my-cv))
    (let ([waiters (cv-waiters my-cv)])
      (if (> waiters 0)

        ; if we have waiting threads, signal one of them
        (begin
          (set-cv-waiters! my-cv (- waiters 1))
          ; increment the counting semaphore to wake up a thread
          (semaphore-post (cv-countingSem my-cv))
          ; wait for the thread to tell us it's okay to proceed
          (semaphore-wait (cv-handshakeSem my-cv))
          )

        ; otherwise, do nothing
        (void)
        )
       ; unlock access to waiters
       (semaphore-post (cv-waitersLock my-cv))
       ))

; BROADCAST HELPERS

; for (int i = 0; i < waiters; i++) s.V();
(define (broadcast-for-helper my-cv i)
    (if (= i 0)
      ; if i is zero, we're done
      (void)
      ; otherwise, we signal one waiting thread, decrement i, and keep going
      (begin
        (semaphore-post (cv-countingSem my-cv))

        (broadcast-for-helper my-cv (- i 1))
        )))

; while (waiters > 0) { waiters--; h.P(); }
(define (broadcast-while-helper my-cv waiters)
    (if (= waiters 0)
      ; if waiters is 0, we're done
      (void)
      ; otherwise, wait for "waiters" many threads to tell us they're awake
      (begin
        (semaphore-wait (cv-handshakeSem my-cv))
        (broadcast-while-helper my-cv (- waiters 1))
        )))

; BROADCAST
(define (blodwen-cv-broadcast my-cv)
    ; lock access to waiters
    (semaphore-wait (cv-waitersLock my-cv))
    (let ([waiters (cv-waiters my-cv)])
      ; signal "waiters" many threads; counting *until* 0 in the helper
      ; function, hence "waiters" and NOT "waiters - 1"
      (broadcast-for-helper my-cv waiters)
      ; wait on "waiters" many threads to have been woken
      (broadcast-while-helper my-cv waiters)
      ; unlock access to waiters
      (semaphore-post (cv-waitersLock my-cv))
      ))

; FIXME: Maybe later. Possibly difficult because of the handshake thingy?
;(define (blodwen-cv-wait-timeout my-cv lockM timeout)
;  ;; precondition: calling thread holds lockM
;   (semaphore-wait (cv-waitersLock my-cv))                 ; x.P()
;   (set-cv-waiters! my-cv (+ (cv-waiters my-cv) 1)) ; waiters++
;   (semaphore-post (cv-waitersLock my-cv))                 ; x.V()
;   (blodwen-mutex-release lockM)                    ; m.Release()
;
;   (sync/timeout (/ timeout 1000000) (cv-countingSem my-cv))
;
;   (semaphore-wait (cv-countingSem my-cv))                 ; s.P()
;   (semaphore-post (cv-handshakeSem my-cv))                 ; h.V()
;   (blodwen-mutex-acquire lockM)                    ; m.Acquire()
;   )


(define (blodwen-make-future work) (future work))
(define (blodwen-await-future ty future) (touch future))

;; NB: These should *ALWAYS* be used in multi-threaded programs since Racket
;; threads are green/virtual threads and so using an external function will
;; block the *entire* runtime until the function returns. This is fine for most
;; things, but not for `sleep`.
(define (blodwen-sleep s) (sleep s))
(define (blodwen-usleep us) (sleep (* 0.000001 us)))

(define (blodwen-clock-time-utc) (current-time 'time-utc))
(define (blodwen-clock-time-monotonic) (current-time 'time-monotonic))
(define (blodwen-clock-time-duration) (current-time 'time-duration))
(define (blodwen-clock-time-process) (current-time 'time-process))
(define (blodwen-clock-time-thread) (current-time 'time-thread))
(define (blodwen-clock-time-gccpu) 0) ;; unsupported
(define (blodwen-clock-time-gcreal) 0) ;; unsupported
(define (blodwen-is-time? clk) (if (time? clk) 1 0))
(define (blodwen-clock-second time) (time-second time))
(define (blodwen-clock-nanosecond time) (time-nanosecond time))

(define (blodwen-arg-count)
  (+ (vector-length (current-command-line-arguments)) 1))

(define (blodwen-arg n)
  (cond
    ((= n 0) (path->string (find-system-path 'run-file)))
    ((< n (+ (vector-length (current-command-line-arguments)) 1))
        (vector-ref (current-command-line-arguments) (- n 1)))
     (else "")))

;; Randoms
(random-seed (date*-nanosecond (current-date))) ; initialize random seed

(define (blodwen-random-seed s) (random-seed s))
(define blodwen-random
  (case-lambda
    ;; no argument, pick a real value from [0, 1.0)
    [() (random)]
    ;; single argument k, pick an integral value from [0, k)
    [(k) (if (> k 0)
           (random k)
           (raise 'blodwen-random-invalid-range-argument))]))

;; For finalisers

(define (blodwen-register-object obj proc)
   (register-finalizer obj (lambda (ptr) ((proc ptr) 'erased)))
   obj)

;; For creating and reading back scheme objects

(define ns (make-base-namespace))

; read a scheme string and evaluate it, returning 'Just result' on success
; TODO: catch exception!
(define (blodwen-eval-scheme str)
  (with-handlers ([exn:fail? (lambda (x) '())]) ; Nothing on failure
     (box (eval (read (open-input-string str)) ns))) ; box == Just
)

(define (blodwen-eval-okay obj)
  (if (null? obj)
      0
      1))

(define (blodwen-get-eval-result obj)
  (unbox obj))

(define (blodwen-debug-scheme obj)
  (display obj) (newline))

(define (blodwen-is-number obj)
  (if (number? obj) 1 0))

(define (blodwen-is-integer obj)
  (if (and (number? obj) (exact? obj)) 1 0))

(define (blodwen-is-float obj)
  (if (flonum? obj) 1 0))

(define (blodwen-is-char obj)
  (if (char? obj) 1 0))

(define (blodwen-is-string obj)
  (if (string? obj) 1 0))

(define (blodwen-is-procedure obj)
  (if (procedure? obj) 1 0))

(define (blodwen-is-symbol obj)
  (if (symbol? obj) 1 0))

(define (blodwen-is-vector obj)
  (if (vector? obj) 1 0))

(define (blodwen-is-nil obj)
  (if (null? obj) 1 0))

(define (blodwen-is-pair obj)
  (if (pair? obj) 1 0))

(define (blodwen-is-box obj)
  (if (box? obj) 1 0))

(define (blodwen-make-symbol str)
  (string->symbol str))

; The below rely on checking that the objects are the right type first.

(define (blodwen-vector-ref obj i)
  (vector-ref obj i))

(define (blodwen-vector-length obj)
  (vector-length obj))

(define (blodwen-vector-list obj)
  (vector->list obj))

(define (blodwen-unbox obj)
  (unbox obj))

(define (blodwen-apply obj arg)
  (obj arg))

(define (blodwen-force obj)
  (obj))

(define (blodwen-read-symbol sym)
  (symbol->string sym))

(define (blodwen-id x) x)
