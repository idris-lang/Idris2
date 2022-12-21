(define (blodwen-os)
  (case (machine-type)
    [(i3le ti3le a6le ta6le tarm64le) "unix"]  ; GNU/Linux
    [(i3ob ti3ob a6ob ta6ob tarm64ob) "unix"]  ; OpenBSD
    [(i3fb ti3fb a6fb ta6fb tarm64fb) "unix"]  ; FreeBSD
    [(i3nb ti3nb a6nb ta6nb tarm64nb) "unix"]  ; NetBSD
    [(i3osx ti3osx a6osx ta6osx tarm64osx) "darwin"]
    [(i3nt ti3nt a6nt ta6nt tarm64nt) "windows"]
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
  (if (logbit? bits x)
      (logor x (ash -1 bits))
      (logand x (sub1 (ash 1 bits)))))

(define (blodwen-toUnsignedInt x bits)
  (logand x (sub1 (ash 1 bits))))

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

(define (integer->bits8 x) (logand x (sub1 (ash 1 8))))
(define (integer->bits16 x) (logand x (sub1 (ash 1 16))))
(define (integer->bits32 x) (logand x (sub1 (ash 1 32))))
(define (integer->bits64 x) (logand x (sub1 (ash 1 64))))

(define (bits16->bits8 x) (logand x (sub1 (ash 1 8))))
(define (bits32->bits8 x) (logand x (sub1 (ash 1 8))))
(define (bits64->bits8 x) (logand x (sub1 (ash 1 8))))
(define (bits32->bits16 x) (logand x (sub1 (ash 1 16))))
(define (bits64->bits16 x) (logand x (sub1 (ash 1 16))))
(define (bits64->bits32 x) (logand x (sub1 (ash 1 32))))

(define (blodwen-bits-shl-signed x y bits) (blodwen-toSignedInt (ash x y) bits))

(define (blodwen-bits-shl x y bits) (logand (ash x y) (sub1 (ash 1 bits))))

(define blodwen-shl (lambda (x y) (ash x y)))
(define blodwen-shr (lambda (x y) (ash x (- y))))
(define blodwen-and (lambda (x y) (logand x y)))
(define blodwen-or (lambda (x y) (logor x y)))
(define blodwen-xor (lambda (x y) (logxor x y)))

(define cast-num
  (lambda (x)
    (if (number? x) x 0)))
(define destroy-prefix
  (lambda (x)
    (cond
      ((equal? x "") "")
      ((equal? (string-ref x 0) #\#) "")
      (else x))))

(define exact-floor
  (lambda (x)
    (inexact->exact (floor x))))

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
          (if (> b l)
              ""
              (substring s b end))))

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
        (let ((str (get-line p)))
            (if (eof-object? str)
                ""
                str))
        void))

(define (blodwen-get-char p)
    (if (port? p)
        (let ((chr (get-char p)))
            (if (eof-object? chr)
                #\nul
                chr))
        void))

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

(define-record thread-handle (semaphore))

(define (blodwen-thread proc)
  (let [(sema (blodwen-make-semaphore 0))]
    (fork-thread (lambda () (proc (vector 0)) (blodwen-semaphore-post sema)))
    (make-thread-handle sema)
    ))

(define (blodwen-thread-wait handle)
  (blodwen-semaphore-wait (thread-handle-semaphore handle)))

;; Thread mailboxes

(define blodwen-thread-data
  (make-thread-parameter #f))

(define (blodwen-get-thread-data ty)
  (blodwen-thread-data))

(define (blodwen-set-thread-data ty a)
  (blodwen-thread-data a))

;; Semaphore

(define-record semaphore (box mutex condition))

(define (blodwen-make-semaphore init)
  (make-semaphore (box init) (make-mutex) (make-condition)))

(define (blodwen-semaphore-post sema)
  (with-mutex (semaphore-mutex sema)
    (let [(sema-box (semaphore-box sema))]
      (set-box! sema-box (+ (unbox sema-box) 1))
      (condition-signal (semaphore-condition sema))
    )))

(define (blodwen-semaphore-wait sema)
  (with-mutex (semaphore-mutex sema)
    (let [(sema-box (semaphore-box sema))]
      (when (= (unbox sema-box) 0)
        (condition-wait (semaphore-condition sema) (semaphore-mutex sema)))
      (set-box! sema-box (- (unbox sema-box) 1))
      )))

;; Barrier

(define-record barrier (count-box num-threads mutex cond))

(define (blodwen-make-barrier num-threads)
  (make-barrier (box 0) num-threads (make-mutex) (make-condition)))

(define (blodwen-barrier-wait barrier)
  (let [(count-box (barrier-count-box barrier))
        (num-threads (barrier-num-threads barrier))
        (mutex (barrier-mutex barrier))
        (condition (barrier-cond barrier))]
    (with-mutex mutex
    (let* [(count-old (unbox count-box))
           (count-new (+ count-old 1))]
      (set-box! count-box count-new)
      (if (= count-new num-threads)
          (condition-broadcast condition)
          (condition-wait condition mutex))
      ))))

;; Channel
; With thanks to Alain Zscheile (@zseri) for help with understanding condition
; variables, and figuring out where the problems were and how to solve them.

(define-record channel (read-mut read-cv read-box val-cv val-box))

(define (blodwen-make-channel ty)
  (make-channel
    (make-mutex)
    (make-condition)
    (box #t)
    (make-condition)
    (box '())
    ))

; block on the read status using read-cv until the value has been read
(define (channel-put-while-helper chan)
  (let ([read-mut (channel-read-mut chan)]
        [read-box (channel-read-box chan)]
        [read-cv  (channel-read-cv  chan)]
        )
    (if (unbox read-box)
      (void)    ; val has been read, so everything is fine
      (begin    ; otherwise, block/spin with cv
        (condition-wait read-cv read-mut)
        (channel-put-while-helper chan)
        )
      )))

(define (blodwen-channel-put ty chan val)
  (with-mutex (channel-read-mut chan)
    (channel-put-while-helper chan)
    (let ([read-box (channel-read-box chan)]
          [val-box  (channel-val-box  chan)]
          )
      (set-box! val-box val)
      (set-box! read-box #f)
      ))
  (condition-signal (channel-val-cv chan))
  )

; block on the value until it has been set
(define (channel-get-while-helper chan)
  (let ([read-mut (channel-read-mut chan)]
        [read-box (channel-read-box chan)]
        [val-cv   (channel-val-cv   chan)]
        )
    (if (unbox read-box)
      (begin
        (condition-wait val-cv read-mut)
        (channel-get-while-helper chan)
        )
      (void)
      )))

(define (blodwen-channel-get ty chan)
  (mutex-acquire (channel-read-mut chan))
  (channel-get-while-helper chan)
  (let* ([val-box  (channel-val-box  chan)]
         [read-box (channel-read-box chan)]
         [read-cv  (channel-read-cv  chan)]
         [the-val  (unbox val-box)]
         )
    (set-box! val-box '())
    (set-box! read-box #t)
    (mutex-release (channel-read-mut chan))
    (condition-signal read-cv)
    the-val))

;; Mutex

(define (blodwen-make-mutex)
  (make-mutex))
(define (blodwen-mutex-acquire mutex)
  (mutex-acquire mutex))
(define (blodwen-mutex-release mutex)
  (mutex-release mutex))

;; Condition variable

(define (blodwen-make-condition)
  (make-condition))
(define (blodwen-condition-wait condition mutex)
  (condition-wait condition mutex))
(define (blodwen-condition-wait-timeout condition mutex timeout)
  (let* [(sec (div timeout 1000000))
         (micro (mod timeout 1000000))]
    (condition-wait condition mutex (make-time 'time-duration (* 1000 micro) sec))))
(define (blodwen-condition-signal condition)
  (condition-signal condition))
(define (blodwen-condition-broadcast condition)
  (condition-broadcast condition))

;; Future

(define-record future-internal (result ready mutex signal))
(define (blodwen-make-future work)
  (let ([future (make-future-internal #f #f (make-mutex) (make-condition))])
    (fork-thread (lambda ()
      (let ([result (work)])
        (with-mutex (future-internal-mutex future)
          (set-future-internal-result! future result)
          (set-future-internal-ready! future #t)
          (condition-broadcast (future-internal-signal future))))))
    future))
(define (blodwen-await-future ty future)
  (let ([mutex (future-internal-mutex future)])
    (with-mutex mutex
      (if (not (future-internal-ready future))
          (condition-wait (future-internal-signal future) mutex))
      (future-internal-result future))))

(define (blodwen-sleep s) (sleep (make-time 'time-duration 0 s)))
(define (blodwen-usleep s)
  (let ((sec (div s 1000000))
        (micro (mod s 1000000)))
       (sleep (make-time 'time-duration (* 1000 micro) sec))))

(define (blodwen-clock-time-utc) (current-time 'time-utc))
(define (blodwen-clock-time-monotonic) (current-time 'time-monotonic))
(define (blodwen-clock-time-duration) (current-time 'time-duration))
(define (blodwen-clock-time-process) (current-time 'time-process))
(define (blodwen-clock-time-thread) (current-time 'time-thread))
(define (blodwen-clock-time-gccpu) (current-time 'time-collector-cpu))
(define (blodwen-clock-time-gcreal) (current-time 'time-collector-real))
(define (blodwen-is-time? clk) (if (time? clk) 1 0))
(define (blodwen-clock-second time) (time-second time))
(define (blodwen-clock-nanosecond time) (time-nanosecond time))


(define (blodwen-arg-count)
  (length (command-line)))

(define (blodwen-arg n)
  (if (< n (length (command-line))) (list-ref (command-line) n) ""))

(define (blodwen-hasenv var)
  (if (eq? (getenv var) #f) 0 1))

;; Randoms
(define random-seed-register 0)
(define (initialize-random-seed-once)
  (if (= (virtual-register random-seed-register) 0)
      (let ([seed (time-nanosecond (current-time))])
        (set-virtual-register! random-seed-register seed)
        (random-seed seed))))

(define (blodwen-random-seed seed)
  (set-virtual-register! random-seed-register seed)
  (random-seed seed))
(define blodwen-random
  (case-lambda
    ;; no argument, pick a real value from [0, 1.0)
    [() (begin
          (initialize-random-seed-once)
          (random 1.0))]
    ;; single argument k, pick an integral value from [0, k)
    [(k)
      (begin
        (initialize-random-seed-once)
        (if (> k 0)
              (random k)
              (assertion-violationf 'blodwen-random "invalid range argument ~a" k)))]))

;; For finalisers

(define blodwen-finaliser (make-guardian))
(define (blodwen-register-object obj proc)
  (let [(x (cons obj proc))]
       (blodwen-finaliser x)
       x))
(define blodwen-run-finalisers
  (lambda ()
    (let run ()
      (let ([x (blodwen-finaliser)])
        (when x
          (((cdr x) (car x)) 'erased)
          (run))))))

;; For creating and reading back scheme objects

; read a scheme string and evaluate it, returning 'Just result' on success
; TODO: catch exception!
(define (blodwen-eval-scheme str)
  (guard
     (x [#t '()]) ; Nothing on failure
     (box (eval (read (open-input-string str)))))
  ); box == Just

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
