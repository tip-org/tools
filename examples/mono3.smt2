(declare-datatypes (a) ((unit (value))))
(define-funs-rec
  ((par (a) (make-unit () (unit a))))
  ((_ value a)))
(prove
  (= (_ make-unit Int)
     (_ value Int)))
