(declare-sort a 0)
(declare-datatypes (b) ((box (make_box (content b)))))
(prove (forall ((xs (box a)) (ys (box a))) (= xs ys)))
