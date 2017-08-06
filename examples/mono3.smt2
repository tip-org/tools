(declare-datatypes (a) ((unit (value))))
(define-funs-rec
  ((par (a) (make-unit () (unit a))))
  ((as value (unit a))))
(prove
  (= (as make-unit (unit Int))
     (as value (unit Int))))
