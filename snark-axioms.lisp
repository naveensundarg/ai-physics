(in-package :snark-user)
(defun snark-declarations ()
  (declare-sort 'Qf)

  (declare-sort 'Qt)
  (declare-sort 'Qq)

  (declare-sort 'Bd :subsorts-incompatible t)
  (declare-subsort 'IB 'Bd)
  (declare-subsort 'Ph 'Bd)

  (declare-function '+ 2 :sort '(Qf Qf Qf))
  (declare-function '- 2 :sort '(Qf Qf Qf))

  (declare-function '* 2 :sort '(Qf Qf Qf))

  (declare-function 'neg 1 :sort '(Qf Qf))
  (declare-function 'inv 1 :sort '(Qf Qf))

  (declare-function 'div 2 :sort '(Qf Qf Qf))

  (declare-function 'sqrt 1 :sort '(Qf Qf))
  
  (declare-function 'sq 1 :sort '(Qf Qf))

  (declare-relation '< 2 :sort '(Qf Qf))
  (declare-relation '> 2 :sort '(Qf Qf))
  (declare-relation '<_ 2 :sort '(Qf Qf))
  (declare-relation '>_ 2 :sort '(Qf Qf))

  (declare-relation 'perp-t 2 :sort '(Qt Qt))
  (declare-function 'vec-t 3 :sort '(Qt Qf Qf Qf))
  (declare-function 'vec-q 4 :sort '(Qq Qf Qf Qf Qf))

  (declare-function 'cs 1 :sort '(Qt Qq))
  (declare-function 'ct 1 :sort '(Qf Qq))

  (declare-function 'c1 1 :sort '(Qf Qq))
  (declare-function 'c2 1 :sort '(Qf Qq))
  (declare-function 'c3 1 :sort '(Qf Qq))
  (declare-function 'c4 1 :sort '(Qf Qq))

  (declare-function '+t 2 :sort '(Qt Qt Qt))
  (declare-function '-t 2 :sort '(Qt Qt Qt))

  (declare-function '+q 2 :sort '(Qq Qq Qq))
  (declare-function '-q 2 :sort '(Qq Qq Qq))

  (declare-function 'mod   1 :sort '(Qf Qf))
  (declare-function 'mod-t 1 :sort '(Qf Qt))
  (declare-function 'mod-q 1 :sort '(Qf Qq))

  (declare-function 'speed 2 :sort '(Qf Qq Qq))
  (declare-function 'space 2 :sort '(Qf Qq Qq))
  (declare-function 'time 2 :sort '(Qf Qq Qq))
  (declare-constant 'k0 :sort 'Qf)
  (declare-constant   'k1 :sort 'Qf)

  ;; constants used in Theorem 1
  (declare-constant 'zs1 :sort 'Qt)
  (declare-constant 'zt1 :sort 'Qf)
  (declare-constant 'z1 :sort 'Qq) (Fora)
  
  (declare-constant 'zs2 :sort 'Qt)
  (declare-constant 'zt2 :sort 'Qf)
  (declare-constant 'z2 :sort 'Qq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;; Field axioms ;;;;;;;;;;;;;;;;;
(defparameter *add-associativity* 
  '(forall ((?x Qf) (?y Qf) (?z Qf))
      (= (+ (+ ?x ?y) ?z) (+ ?x (+ ?y ?z)))))
(defparameter *mult-associativity* 
  '(forall ((?x Qf) (?y Qf) (?z Qf))
       (= (* (* ?x ?y) ?z) (* ?x (* ?y ?z)))))
(defparameter *add-commutativity*
  '(forall ((?x Qf) (?y Qf))
       (= (+ ?x ?y) (+ ?y ?x))))
(defparameter *mult-commutativity*
  '(forall ((?x Qf) (?y Qf))
       (= (* ?x ?y) (* ?y ?x))))
(defparameter *add-distributivity*
  '(forall ((?x Qf) (?y Qf) (?z Qf))
       (= (* ?x (+ ?y  ?z)) (+ (* ?x ?y) (* ?x ?z)))))
(defparameter *add-identity*
  '(forall ((?x Qf))
       (= (+ ?x k0) ?x )))
(defparameter *mult-identity*
  '(forall ((?x Qf))
       (= (* ?x k1) ?x )))
(defparameter *add-inverse*
  '(forall ((?x Qf))
       (= (+ ?x (neg ?x)) k0)))
(defparameter *mult-inverse*
  '(forall ((?x Qf))
       (implies (not (= ?x k0))
	   (= (* ?x (inv ?x)) k1))))

(defparameter *not-k0-k1*
  '(not (= k0 k1)))

(defparameter *no-zero-divisors*
  '(forall ((?x Qf) (?y Qf))
    (implies (= (* ?x ?y) k0) (or (= ?x k0) (= ?y k0)))))

(defparameter *square*
  '(forall ((?x Qf))
    (= (sq ?x) (* ?x ?x))))

(defparameter *square-root*
  '(forall ((?x Qf) (?y Qf))
    (implies (>_ ?x k0) 
     (impliesf 
      (= (sqrt ?x) ?y)
      (and (>_ ?y k0 ) (= (sq ?y) ?x))))))

(defparameter *total-order-def-1*
  '(forall ((?x Qf) (?y Qf))
    (implies 
     (<_ ?x ?y)
     (exists ((?z Qf)) (= (+ ?x (sq ?z)) ?y)))))

(defparameter *total-order-def-2*
  '(forall ((?x Qf) (?y Qf))
    (implies
     (exists ((?z Qf)) (= (+ ?x (sq ?z)) ?y))
     (<_ ?x ?y))))

(defparameter *total-order-1*
  '(forall (( ?x Qf) (?y Qf))
       (or (<_ ?x ?y) (<_ ?y ?x))))
(defparameter *total-order-2*
  '(forall ((?x Qf) (?y Qf))
       (implies  (and (<_ ?x ?y) (<_ ?y ?x))
	    (= ?x ?y))))
(defparameter *trans*
  '(forall ((?x Qf) (?y Qf) (?z Qf))
       (implies (and (<_ ?x ?y) (<_ ?y ?z))
	   (<_ ?x ?z))))

(defparameter *pos-elems-squares*
  '(forall ((?x Qf))
    (exists ((?y Qf))
     (or 
      (= ?x (sq ?y))
      (= (neg ?x) (sq ?y))))))

(defparameter *def-<*
  '(forall ((?x Qf) (?y Qf))
    (implies (<_ ?x ?y)
      (or (= ?x ?y) (< ?x ?y)))))

(defparameter *def->1*
  '(forall ((?x Qf) (?y Qf))
    (impliesf 
      (< ?x ?y)
      (> ?y ?x))))

(defparameter *def->2*
  '(forall ((?x Qf) (?y Qf))
    (implies (>_ ?x ?y)
      (or (= ?x ?y) (> ?x ?y)))))

(defparameter *add-ordering*
  '(forall ((?x Qf) (?y Qf) (?z Qf))
       (implies (< ?x ?y)
	   (< (+ ?x ?z) (+ ?y ?z) ))))

(defparameter *mult-ordering*
  '(forall ((?x Qf) (?y Qf))
       (implies (and  (< k0 ?x) (< k0 ?y))
	   (< k0 (* ?x ?y)))))




(defparameter *field-axioms* 
  (list
   *add-associativity* *mult-associativity* 
   *add-commutativity* *mult-commutativity*
   *add-distributivity* 
   *add-identity* *mult-identity*
   *add-inverse* *mult-inverse* *not-k0-k1* *no-zero-divisors*
   *total-order-def-1* *total-order-def-2* *total-order-1* *total-order-2* *trans*
   *add-ordering* *mult-ordering*
   *square* *square-root*
   *pos-elems-squares*))


(defparameter *vec-q*
  '(forall ((?x Qq))
	  (exists ((?x1 Qf) (?x2 Qf) (?x3 Qf) (?x4 Qf))
		  (= ?x (vec-q ?x1 ?x2 ?x3 ?x4)))))

(defparameter *vec-t*
  '(forall ((?x Qt))
	  (exists ((?x1 Qf) (?x2 Qf) (?x3 Qf))
		  (= ?x (vec-t ?x1 ?x2 ?x3)))))


(defparameter *vec-t-unique*
  '(forall ((?x Qt) 
	    (?x1 Qf) (?x2 Qf) (?x3 Qf)
	    (?y1 Qf) (?y2 Qf) (?y3 Qf))
    (implies (and 
	      (= ?x (vec-t ?x1 ?x2 ?x3))
	      (= ?x (vec-t ?y1 ?y2 ?y3)))
     (and  
      (= ?x1 ?y1)
      (= ?x2 ?y2)
      (= ?x3 ?y3)))))

(defparameter *vec-q-unique*
  '(forall ((?x Qq) 
	    (?x1 Qf) (?x2 Qf) (?x3 Qf) (?x4 Qf)
	    (?y1 Qf) (?y2 Qf) (?y3 Qf) (?y4 Qf))
    (implies (and 
	      (= ?x (vec-q ?x1 ?x2 ?x3 ?x4))
	      (= ?x (vec-q ?y1 ?y2 ?y3 ?y4)))
     (and  
      (= ?x1 ?y1)
      (= ?x2 ?y2)
      (= ?x3 ?y3)
      (= ?x4 ?y4)))))

(defparameter *ci*
  '(forall ((?x Qq) (?x1 Qf) (?x2 Qf)  (?x3 Qf) (?x4 Qf))
    (impliesf 
     (= ?x (vec-q ?x1 ?x2 ?x3 ?x4))
     (and 
      (= (c1 ?x) ?x1)
      (= (c2 ?x) ?x2)
      (= (c3 ?x) ?x3)
      (= (c4 ?x) ?x4)))))

(defparameter *-f*
  '(forall ((?x Qf) (?y Qf))
    (= (- ?x ?y) (+ ?x (neg ?y)))))
(defparameter *space*
  '(forall ((?x Qq) (?y Qq ))
    (= 
     (space ?x ?y)
     (mod-t (-t (cs ?x) (cs ?y))))))

(defparameter *time*
  '(forall ((?x Qq) (?y Qq ))
    (= 
     (time ?x ?y)
     (mod (- (ct ?x) (ct ?y))))))

(defparameter *speed*
  '(forall ((?x Qq) (?y Qq))
    (= (speed ?x ?y)
     (div (space ?x ?y) (time ?x ?y)))))

(defparameter *div*
  '(forall ((?x Qf) (?y Qf))
    (= (div ?x ?y) (* ?x (inv ?y)))))
(defparameter *ortho-t*
  '(forall ((?x Qq) (?y Qq))
    (impliesf 
     (perp-t (cs ?x) (cs ?y))
     (= k0 (+ (* (c1 ?x) (c1 ?y))
	      (+ (* (c2 ?x) (c2 ?y))
		 (* (c3 ?x) (c3 ?y))))))))

(defparameter *cs*
  '(forall ((?x Qq))
    (= (cs ?x) (vec-t (c1 ?x) (c2 ?x) (c3 ?x) ))))

(defparameter *ct*
  '(forall ((?x Qq))
    (= (ct ?x) (c4 ?x))))

(defparameter *defs*  
  (list 
   *div*
   *space* *time* *speed*
   *vec-q* *vec-t*
   *vec-t-unique* *vec-q-unique*
   *ortho-t*
   *cs* *ct*
    *-f*))


(defparameter *zs-2*
  '(forall ((?x Qq) (?y Qq))
    (= (zs2 ?x ?y)  
     (+t 
      (*ft 
       (ws ?x ?y)
       (div (sq (time ?x ?y))
	    (space ?x ?y)))
      (*ft 
       (ws-perp ?x ?y)
       (div (* (time ?x ?y) (sqrt (-f (sq (space ?x ?y))
				      (sq (time ?x ?y)))))
	    (space ?x ?y)))))))

(defparameter *zt-2*
  '(forall ((?x Qq) (?y Qq))
    (= (zt2 ?x ?y)
     (ct ?y))))


(defparameter *axioms* (append *field-axioms* *defs* ))
(mapcar 'assert *axioms*)

;; (forall (z x1 x2 x3 x4 y1 y2 y3 y4)
;;   (if (and (Q x1) (Q x2) (Q x3) (Q x4) (Q y1) (Q y2) (Q y3) (Q y4) (Q4 z))
;;      (if (and (= z (vec-q x1 x2 x3 x4)) (= z (vec-q y1 y2 y3 y4)))
;; 	(and (= x1 y1) (= x2 y2) (= x3 y3) (= x4 y4))

;; (forall (x y)
;; 	(if (and (Q4 x) (Q4 y))
;; 	    (= (speed x y)
;; 	       (/  (sqrt  (+ (sq (- (c1 x) (c1 y))) 
;; 			     (+ (sq (- (c2 x) (c2 y))) 
;; 				(sq (- (c3 x) (c3 y)))))) 
;; 		   (sqrt (sq (- (c4 x) (c4 y))))))))


;; (forall (x x1 x2 x3 x4) 
;;     (if (and (Q4 x) (Q x1) (Q x2) (Q x3) (Q x4))
;; 	(if (= x (vec-q x1 x2 x3 x4))
;; 	    (and (= x1 (c1 x))
;; 		  (= x2 (c2 x))
;; 		  (= x3 (c3 x))
;; 		  (= x4 (c4 x))))))



;; (forall (x y)
;; 	(if (and (Q4 x) (Q4 y))
;; 	    (= (speed x y)
;; 	       (/  (sqrt  (+ (sq (- (c1 x) (c1 y))) 
;; 			     (+ (sq (- (c2 x) (c2 y))) 
;; 				(sq (- (c3 x) (c3 y)))))) 
;; 		   (sqrt (sq (- (c4 x) (c4 y))))))))




;; 	       (/  (sqrt  (+ (sq (- a1 (+ a1 1))) 
;; 			     (+ (sq (- a2 a2)) 
;; 				(sq (- a3 a3))))) 
;; 		   (sqrt (sq (- a4 (+ a4 1)))))