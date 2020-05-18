;; Copyright 2009 Marc Feeley <feeley@iro.umontreal.ca>
;; Licensed under Apache 2.0 or LGPL 2.1

(define-macro (define-c-struct type . fields)
  (let* ((type-str
           (symbol->string type))
         (struct-type-str
           (string-append "struct " type-str))
         (release-type-str
           (string-append "release_" type-str))
         (sym
           (lambda strs (string->symbol (apply string-append strs))))
         (type*
           (sym type-str "*"))
         (type*/nonnull
           (sym type-str "*/nonnull"))
         (type*/release-rc
           (sym type-str "*/release-rc"))
         (expansion
           `(begin

             ;; Release function which is called when the object
             ;; is no longer accessible from the Scheme world

             (c-declare
               ,(string-append
                  "static ___SCMOBJ " release-type-str "(void* ptr)\n"
                  "{\n"
                  "  ___EXT(___release_rc)(ptr);\n"
                  "  return ___FIX(___NO_ERR);\n"
                  "}\n"))

             ;; C types

             (c-define-type ,type (struct ,type-str))
             (c-define-type ,type* (pointer ,type (,type*)))
             (c-define-type ,type*/nonnull (nonnull-pointer ,type (,type*)))
             (c-define-type ,type*/release-rc (nonnull-pointer ,type (,type*) ,release-type-str))

             ;; Type allocator procedure

             (define ,(sym "alloc-" type-str)
               (c-lambda ()
                         ,type*/release-rc
                         ,(string-append "___result_voidstar = ___EXT(___alloc_rc)(sizeof(" struct-type-str "));")))

             ;; Field getters

             ,@(map (lambda (field)
                      (let ((field-str (symbol->string (car field)))
                            (field-type (cadr field)))
                        `(define ,(sym type-str "-" field-str)
                          (c-lambda (,type*/nonnull)
                                    ,field-type
                                    ,(string-append "___result = ___arg1->" field-str ";")))))
                    fields)

             ;; Field setters

             ,@(map (lambda (field)
                      (let ((field-str (symbol->string (car field)))
                            (field-type (cadr field)))
                        `(define ,(sym type-str "-" field-str "-set!")
                          (c-lambda (,type*/nonnull ,field-type)
                                    void
                                    ,(string-append "___arg1->" field-str " = ___arg2;")))))
                    fields))))

             expansion))
