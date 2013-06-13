(in-package :spec-rel)


(defparameter *Sorts*
  (list 
   'Body 'Qs 'Q4 'Q3 'EventSet 
   'Line 'Plane))

(defparameter *Function-Sorts*
  '((line 2 :sort (line Q4 Q4))
    (plane 3 :sort (Plane Q4 Q4 Q4))))

(defun setup-sorts ()
  (mapcar #'snark:declare-sort *Sorts*)

  
  (snark:declare-function 'line 2 :sort '(Line Q4 Q4))
  (snark:declare-function 'plane 3 :sort '(Plane Q4 Q4 Q4))
  (snark:declare-function 'plane 3 :sort '(Plane Q4 Q4 Q4))
  
 
  (snark:declare-relation 'On-line 2 :sort '(Q4 Line))
  (snark:declare-relation 'On-plane 2 :sort '(Q4 Plane))
  (snark:declare-relation 'On-planel 2 :sort '(Line Plane))
  (snark:declare-function 'slope 2 :sort '(Qs Q4 Q4))
  (snark:declare-function 'slopel 1 :sort '(Qs Line ))
  (snark:declare-relation 'Parallel 2 :sort '(Line Line))
    

  (snark:declare-relation 'IB 1 :sort '(Body))
  (snark:declare-relation 'Ob 1 :sort '(Body))
  (snark:declare-relation 'IOb 1 :sort '(Body))
  (snark:declare-relation 'Ph 1 :sort '(Body))
  (snark:declare-relation 'W 3 :sort '(Body Body Q4))
  (snark:declare-relation 'W 3 :sort '(Body Body Q4))
  
  (snark:declare-relation 'In 2 :sort '(EventSet Body))
  (snark:declare-function 'ev 2 :sort '(EventSet Body Q4))

  (snark:declare-relation 'EquivSTDistance 2 :sort  '(Q4 Q4))
  (snark:declare-relation 'greater_space_time_distance 2 :sort  '(Q4 Q4))
  (snark:declare-relation 'lesser_space_time_distance 2 :sort  '(Q4 Q4))

  (snark:declare-relation 'orthogonal_3 2 :sort  '(Q3 Q3))

  (snark:declare-relation 'ABS 3 :sort '(Q4 Q4 Q4))
    
  (snark:declare-relation '> 2 :sort  '(Q4 Q4))
  (snark:declare-relation '< 2 :sort  '(Q4 Q4))

  (snark:declare-function 'space 1 :sort '(Q3 Q4))
  (snark:declare-function 'time 1 :sort '(Qs Q4))
  (snark:declare-function 'm3 1 :sort '(Qs Q3))
  (snark:declare-function 'minus-4 2 :sort '(Q4 Q4 Q4))
  (snark:declare-function 'minus-3 2 :sort '(Q3 Q3 Q3))
  (snark:declare-function 'minus-s 2 :sort '(Qs Qs Qs))
    
  (snark:declare-function 'm1 1 :sort '(Qs Qs))
  (snark:declare-constant 'zero :sort 'Qs)
  (snark:declare-constant 'spacezero :sort 'Q3)
  
  (snark:declare-function 'c1 1 :sort '(Qs Q4))
  (snark:declare-function 'c2 1 :sort '(Qs Q4))
  (snark:declare-function 'c3 1 :sort '(Qs Q4)))



(defun speed-of-light-theorem-sorts ()
    (snark:declare-constant 'x :sort 'Q4)
    (snark:declare-constant 'y :sort 'Q4)
    (snark:declare-constant 'z :sort 'Q4)
    (snark:declare-constant 'w :sort 'Q4)
    (snark:declare-constant 'x1 :sort 'Q4)
    (snark:declare-constant 'y1 :sort 'Q4)
    (snark:declare-constant 'y1 :sort 'Q4)
    (snark:declare-constant 'z1 :sort 'Q4)
    (snark:declare-constant 'w1 :sort 'Q4)
    (snark:declare-constant 'm :sort 'Body)
    (snark:declare-constant 'k :sort 'Body)
    (snark:declare-constant 'p1 :sort 'Body)
    (snark:declare-constant 'p2 :sort 'Body)
    (snark:declare-constant 'p3 :sort 'Body))



(setf !logic-declarations! 
      (lambda () 
	(setup-sorts)
	(speed-of-light-theorem-sorts)))


(defparameter *B-definition*
  '(forall ((?m :sort Body)) (IB ?m)))

(defparameter *Ob-definition*
  '(forall ((?m :sort Body)) 
    (iff (Ob ?m) 
     (exists ((?b :sort Body) (?x :sort Q4)) (W ?m ?b ?x)))))

(defparameter *IOb-definition*
  '(forall ((m  :sort Body)) 
    (iff (IOb m) 
     (and (Ob m) (IB m)))))


(defparameter *AxFd* 
  '(= 0 0))

(defparameter *general-field-lemmas*
  (list 
   '(forall ((?x Qs) (?y Qs))
     (= 
      (m1 (minus-s ?x ?y))
      (m1 (minus-s ?y ?x))))
   '(forall ((?x Q3) (?y Q3))
     (= 
      (m3 (minus-3 ?x ?y))
      (m3 (minus-3 ?y ?x))))))

(defparameter *EquivSTDistance-x-y*
  '(forall ((x :sort Q4) (y :sort Q4))
    (iff (= (m3 (minus-3 (space x) (space y)) )
	  (m1 (minus-s (time x) (time y))))
     (EquivSTDistance x y))))

(defparameter *greater_space_time_distance-x-y*
  '(forall ((x :sort Q4) (y :sort Q4))
    (iff (> (m3 (minus-3 (space x) (space y)) )
	  (m1 (minus-s (time x) (time y))))
     (greater_space_time_distance x y))))

(defparameter *lesser_space_time_distance-x-y*
  '(forall ((x :sort Q4) (y :sort Q4))
    (iff (> (m3 (minus-3 (space x) (space y)) )
	  (m1 (minus-s (time x) (time y))))
     (lesser_space_time_distance x y))))

(defparameter *def-event*
  '(forall ((m :sort Body) (b :sort Body) (x :sort Q4))
    (iff (W m b x) (In (ev m x) b))))

(defparameter *AxPh*
  '(forall ((?m :sort Body))
    (forall ((?x :sort Q4) (?y :sort Q4))
     (implies (IOb ?m)
      (iff 
       (exists ((?p :sort Body)) 
	       (and (Ph ?p) (W ?m ?p ?x) (W ?m ?p ?y)))
       (EquivSTDistance ?x ?y))))))

(defparameter *AxEv*
  '(forall ((?m :sort Body) (?k :sort Body))
    (implies (and (IOb ?m) (IOb ?k))
     (forall ((?x :sort Q4))
      (exists ((?y :sort Q4))
	      (= (ev ?m ?x) (ev ?k ?y)))))))


(defparameter *AxSf*
  '(forall ((?m Body))
    (implies (IOb ?m)
     (forall ((?x Q4))
      (iff (W ?m ?m ?x) 
	   (and 
	    (= (c1 ?x) zero)
	    (= (c2 ?x) zero)
	    (= (c3 ?x) zero)))))))
(defparameter *AxSf-shortened*
  '(forall ((?m Body))
    (implies (IOb ?m)
     (forall ((?x Q4))
      (iff (W ?m ?m ?x) 
	   (= spacezero (space ?x )))))))

(defparameter *Theorem-Neat*
  '(forall ((?x :sort Q4) (?y :sort Q4) (?m :sort Body))
    (implies (and (IOb ?m) (not (= ?x ?y)))
     (not (= (ev ?m ?x) (ev ?m ?y))))))

(setf *axioms*
      (list
       *B-definition*
       *Ob-definition* *IOb-definition*
       *EquivSTDistance-x-y*  *def-event*
       *AxPh* *AxEv* *AxSf* *AxSf-shortened*
       *Theorem-Neat*))
(setf *axiom-names*
      `((,*B-definition* . "Bdefinition")
       (,*Ob-definition* . "Obdefinition") 
       (,*IOb-definition* . "IObdefinition")
       (,*EquivSTDistance-x-y* . "defequivstdistance")  
       (,*def-event* . "defevent")
       ( ,*AxPh* . "AxPh") 
       ( ,*AxEv* . "AxEv") 
       ( ,*AxSf* . "AxSf")
       ( ,*AxSf-shortened* . "AxSfshortened")
       (,*Theorem-Neat* . "TheoremNeat")))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Theorem No Inertial Observer Greater Than The Speed of Light
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;; Branch 2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defparameter *branch-2-assumptions*
  (list '(IOb m) 
	'(IOb k)
	'(not (= x y)) 
	'(W m k x)
	'(not (EquivSTDistance x y))
	'(W m k y)
	'(greater_space_time_distance x y)))

(defparameter *branch-2-properties-of-z*
  '(and 
    (not (= x z)) (not (= y z))
    (not (= (ev m x) (ev m y)))
    (not (= (ev m y) (ev m z)))
    (not (= (ev m z) (ev m x)))
    (EquivSTDistance x z)))
  
(defparameter *branch-2-field-assumptions*
  (list  
   '(forall ((?x :sort Q4) (?y :sort Q4))
     (implies
      (greater_space_time_distance ?x  ?y)
      (and 
       (implies (not (= (time ?x) (time ?y)))
		(exists ((?z :sort Q4))
			(and (EquivSTDistance ?x ?z)
			     (not (= ?z ?x)) (not (= ?z ?y))
			     (not (= zero (m1 (minus-s (time ?x) (time ?y)))))
			     (orthogonal-3 (minus-3 (space ?z) (space ?x)) (minus-3 (space ?z) (space ?y))))))
       (implies (= (time ?x) (time ?y))
		(exists ((?z :sort Q4))
			(and (EquivSTDistance ?x ?z)
			     (not (= ?z ?x)) (not (= ?z ?y))
			     (not (= zero (m1 (minus-s (time ?x) (time ?y)))))
			     (orthogonal-3 (minus-3 (space ?z) (space ?x)) (minus-3 (space ?y) (space ?x)))))))))))
(defparameter *branch-2-abstract-field-assumptions*
  (list  
   '(forall ((?x :sort Q4) (?y :sort Q4))
     (implies
      (greater_space_time_distance ?x  ?y)
      (exists ((?z :sort Q4))
       (and (not (= ?z ?x))
	    (not (= ?z ?y))
	    (ABS ?x ?y ?z)
	    (EquivSTDistance ?x ?z)))))))

(defparameter *branch-2-geometric-lemmas*
  (check-syntax 
   (list 
    ;;G1a
    '(forall ((?x :sort Q4) (?y :sort Q4))
      (iff (EquivSTDistance ?x ?y) (EquivSTDistance ?y ?x)))
    ;;G1b
    '(forall ((?x :sort Q4) (?y :sort Q4) (?z :sort Q4))
      (and 
       (= (plane ?x ?y ?z) (plane ?y ?z ?x))
       (= (plane ?y ?z ?x) (plane ?z ?x ?y))
       (= (plane ?z ?y ?x) (plane ?x ?z ?x ))
       (= (plane ?x ?z ?y) (plane ?y ?x ?z))))
    '(forall ((?x :sort Q4) (?y :sort Q4))
      (On-line ?x (line ?x ?y)))
    ;; G2
    '(forall ((?x :sort Q4) (?y :sort Q4))
      (= (line ?x ?y) (line ?y ?x)))
    ;; G3
    '(forall ((?x :sort Q4) (?y :sort Q4) (?z :sort Q4))
      (implies (and (EquivSTDistance ?x ?y) (EquivSTDistance ?y ?z) (EquivSTDistance ?z ?x))
       (On-line ?z (line ?x ?y))))
    ;; G4
    '(forall ((?x :sort Q4) (?y :sort Q4) (?z :sort Q4) (?t :sort Q4))
      (implies (On-line ?t (line ?x ?y))
       (On-plane ?t (plane ?x ?y ?z))))
    ;; G5
    '(forall ((?l1 :sort Line) (?l2 :sort Line))
      (implies (and (not (= ?l1 ?l2)) (= (slopel ?l1) (slopel ?l2)) (exists ((?p :sort Plane)) (and (On-planel ?l1 ?p) (On-planel ?l2 ?p))))
        (Parallel ?l1 ?l2)))
    ;; G6
    '(forall ((?x :sort Q4) (?y :sort Q4) (?p :sort Q4) (?q :sort Q4))
      (implies (and (EquivSTDistance ?x ?y) (EquivSTDistance ?p ?q))
       (= (slopel (line ?x ?y)) (slopel (line ?p ?q)))))
    ;; G7
    '(forall ((?x :sort Q4) (?y :sort Q4) (?z :sort Q4))
      (On-planel (line ?x ?z) (plane ?x ?y ?z)))
    ;; G8
    '(forall ((?x :sort Q4) (?y :sort Q4) (?z :sort Q4) (?w :sort Q4))
      (implies  (On-line ?w (line ?x ?z)) (On-planel (line ?w ?y) (plane ?x ?y ?z))))
    ;; G9
    '(forall ((?l1 :sort Line) (?l2 :sort Line))
      (implies (Parallel ?l1 ?l2)
       (not (exists ((?w :sort Q4))
		    (and (On-line ?w ?l1) (On-line ?w ?l2))))))
    ;; G10
    '(forall ((?x :sort Q4) (?y :sort Q4) (?w :sort Q4) (?z :sort Q4))
      (implies (and (EquivSTDistance ?x ?z) (On-line ?w (line ?x ?z)) (= (slopel (line ?x ?x)) (slopel (line ?w ?y))))
       (EquivSTDistance ?x ?y))))))


(defparameter *branch-2-final-geometric-1*
  (problem 
   :name "B2-G1"
   :doc "w is on line xz"
   :goal
   '(forall ((?x :sort Q4) (?z :sort Q4) (?w :sort Q4))
     (implies  (and (EquivSTDistance ?x ?z) (EquivSTDistance ?z ?w) (EquivSTDistance ?w ?x))
      (On-line ?w (line ?x ?z))))
   :assumptions *branch-2-geometric-lemmas* ))
(eval-when (:execute) (semi-prove *branch-2-final-geometric-1* :visualize t )) 

(defparameter *branch-2-final-geometric-2*
  (problem 
   :name "B2-G2"
   :doc "w is on plane xyz"   
   :goal
   '(forall ((?x :sort Q4) (?y :sort Q4) (?z :sort Q4) (?w :sort Q4))
     (implies (On-line ?w (line ?x ?y))
      (On-plane ?w (plane ?x ?y ?z))))
   :assumptions *branch-2-geometric-lemmas* ))
(eval-when (:execute) (semi-prove *branch-2-final-geometric-2* :visualize t )) 

(defparameter *branch-2-final-geometric-3*
  (problem 
   :name "B2-G"
   :doc "w is on line x-z and line w-y"
   :goal
   '(forall ((?x :sort Q4) (?y :sort Q4) (?z :sort Q4) (?w :sort Q4))
     (implies (and 
	       (EquivSTDistance ?x ?z) 
	       (EquivSTDistance ?z ?w) 
	       (EquivSTDistance ?w ?x) 
	       (EquivSTDistance ?w ?y)
	       )
      (and (On-line ?w (line ?x ?z)) (On-line ?w (line ?w ?y))
					;   (On-plane w (plane x y z))
					;  (= (slopel (line w y)) (slopel (line x z)))
					; (and (Parallel (line w y) (line x z)))
	       )))
   :axioms nil
   :assumptions  *branch-2-geometric-lemmas* 
   :sub-problems  (list *branch-2-final-geometric-1* *branch-2-final-geometric-2*)))
(eval-when (:execute) (semi-prove *branch-2-final-geometric-3* :visualize t ))  


(defparameter *branch-2-final-geometric-4*
  (problem :goal
	   '(implies 
	     (and  
	      (not (= (slopel (line w y)) (slopel (line x z))))
	      (EquivSTDistance x z)		    
	      (EquivSTDistance w y)
	      (On-line w (line x z)) (On-line w (line w y)))
	     (and (On-plane w (plane x y z))
	      (= (slopel (line w y)) (slopel (line x z)))
	      (and (Parallel (line w y) (line x z))))
	     )
	   :axioms nil
	   :assumptions  *branch-2-geometric-lemmas* 
	   :sub-problems  (list *branch-2-final-geometric-3*)
	   ))
(eval-when (:execute) (semi-prove *branch-2-final-geometric-4* :visualize t )) 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; Branch 2 Final Geometric Part of the Proof;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defparameter *branch-2-final-geometric*
  (problem
   :goal
   '(implies 
     (and 
     ; (not (= (slopel (line w y)) (slopel (line x z))))
      (not (EquivSTDistance x y))
      (EquivSTDistance x z) 
      (EquivSTDistance z w) 
      (EquivSTDistance w x) 
      (EquivSTDistance w y))
     false)
	   
   :doc 
   " If there are 4 points x,y,z, w in m's worldview such that EquiSTDistance(x,z), EquivSTDistance(w,z) EquivSTDistance(x,w) and EquivSTDistance(w,z) we can derive a contradiction."
   :axioms nil
   :assumptions  *branch-2-geometric-lemmas* ))

(eval-when (:execute) (semi-prove *branch-2-final-geometric* :visualize t )) 

(defparameter *Neat-Extension*
  (problem 
   :goal '(forall ((?m :sort Body) (?x :sort Q4) (?y :sort Q4) (?z :sort Q4))
	   (implies (IOb ?m)
	    (iff 
	     (and (not (= ?x ?y)) (not (= ?y ?z)) (not (= ?z ?x)))
	     (and 
	      (not (= (ev ?m ?x) (ev ?m ?y)))
	      (not (= (ev ?m ?y) (ev ?m ?z)))
	      (not (= (ev ?m ?z) (ev ?m ?x)))))))
   :name "Theorem-Neat-3"
   :doc "Theorem Neat for 3 places."
   :axioms (list *Theorem-Neat*)))
;(semi-prove *Neat-Extension*)

(defparameter *B2-1*
  (problem 
   :name "B2-1"
   :doc "There is a z on the light cone at x."
   :goal '(exists ((?z :sort Q4) (?p :sort Body))
	   (EquivSTDistance x ?z))
   :axioms (list *AxPh* *AxEv*)
   :assumptions (append *branch-2-assumptions* *branch-2-field-assumptions*)))

(eval-when (:execute) (semi-prove *B2-1* :visualize t))
(defparameter *B2-2*
  (problem 
   :name "B2-1"
   :doc "There is a photon p that m sees at x and z."
   :goal '(exists ((?z :sort Q4) (?p :sort Body))
	   (and (Ph ?p) (W m ?p x)(W m ?p ?z)))
   :axioms (list *AxPh* )
   :assumptions *branch-2-assumptions*
   :sub-problems (list *B2-1*)))
(eval-when (:execute) (semi-prove *B2-2* :visualize t))

(defparameter *B2-3*
  (problem 
   :name "B2-1"
   :doc "p is in ev(m,x) and ev(m,z)"
   :goal '(exists ((?z :sort Q4) (?p :sort Body))
	   (and (Ph ?p) (In (ev m x) ?p)(In (ev m ?z) ?p)))
   :axioms (list *AxEv* *def-event* )
   :assumptions *branch-2-assumptions*
   :sub-problems (list *B2-2*)))

(eval-when (:execute) (semi-prove *B2-3* :visualize t))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; properties of z ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(progn 
  ;;;; proprerties of z
  (defparameter *B2-4a*
    (problem 
     :name "B2-4a"
     :doc "p is in ev(m,x) and ev(m,z)"
     :goal '(exists ((?z :sort Q4))
	     (and  (not (= x ?z)) (not (= y ?z))))
     :axioms (list *Theorem-Neat*)
     :assumptions  (append *branch-2-assumptions* *branch-2-abstract-field-assumptions*)))
(eval-when (:execute) (semi-prove *B2-4a* :visualize t))


  (defparameter *B2-4b*
    (problem 
     :name "B2-4b"
     :doc "There is a z."
     :goal '(exists ((?z :sort Q4))
	     (and
	      (not (= (ev m x) (ev m y)))
	      (not (= (ev m y) (ev m ?z)))
	      (not (= (ev m ?z) (ev m x)))))
     :axioms (list *Theorem-Neat*)
     :assumptions   *branch-2-assumptions* 
     :sub-problems (list  *B2-4a* *Neat-Extension*)))
(eval-when (:execute) (semi-prove *B2-4b* :visualize t))

  (defparameter *B2-4c*
    (problem 
     :name "B2-4c"
     :doc "x1 not equal to y1"
     :goal '(exists ((?x1 :sort Q4)(?y1 :sort Q4) )
	     (and 
	      (not (= ?x1 ?y1))
	      (= (ev m x) (ev k ?x1))
	      (= (ev m y) (ev k ?y1))))
     :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
     :assumptions *branch-2-assumptions*))
(eval-when (:execute) (semi-prove *B2-4c* :visualize t))


  (defparameter *B2-4d*
    (problem 
     :name "B2-4d"
     :doc "There is a z."
     :goal '(exists ((?z :sort Q4))
	     (and
	      (EquivSTDistance x ?z)))
     :axioms (list *Theorem-Neat* *AxPh* *def-event* *EquivSTDistance-x-y*)
     :assumptions  (append *branch-2-assumptions* *branch-2-field-assumptions*) 
     :sub-problems (list  *B2-4a* *Neat-Extension*))))
(eval-when (:execute) (semi-prove *B2-4d* :visualize t))

(defparameter *B2-4*
  (problem 
   :name "B2-4"
   :doc "There is a z."
   :goal '(exists ((?x :sort Q4) (?y :sort Q4) (?z :sort Q4))
	   (and
	    (not (= (ev m x) (ev m y)))
	    (not (= (ev m y) (ev m ?z)))
	    (not (= (ev m ?z) (ev m x)))))
   :axioms (list *Theorem-Neat*)
   :assumptions   *branch-2-assumptions* 
   :sub-problems (list  *B2-4a* *Neat-Extension*)))
(eval-when (:execute) (semi-prove *B2-4* :visualize t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;; Properties of z;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *properties-of-z*
  (list '(and (EquivSTDistance x z))
	'(and
	 (not (= (ev m x) (ev m y)))
	 (not (= (ev m y) (ev m z)))
	 (not (= (ev m z) (ev m x))))
	'(and  (not (= x z)) (not (= y z)))))

(defparameter *B2-5*
  (problem 
   :name "B2-5"
   :doc "There are x1, y1, z1"
   :goal 
   '(exists ((?x1 :sort Q4)(?y1 :sort Q4) (?z1 :sort Q4)  )
	     (and 
	      (not (= ?x1 ?y1)) ; (not (= ?y1 ?z1)) (not (= ?z1 ?x1))
	      (= (ev m x) (ev k ?x1))
	      (= (ev m y) (ev k ?y1))
	      (= (ev m z) (ev k ?z1))
	     (= (space ?x1) spacezero)
	     (= (space ?y1) spacezero)
	      ))
   :axioms (list  *AxPh* *AxEv*  *AxSf* *AxSf-shortened*  *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*
		 )
   :assumptions (append *properties-of-z* *branch-2-assumptions*)
   :sub-problems (list *B2-4c*)))
(eval-when (:execute) (semi-prove *B2-5* :verbose t :visualize t))


(defparameter *properties-of-x1y1z1*
  (list   '(and 
	    (not (= x1 y1))
	    (= (ev m x) (ev k x1))
	    (= (ev m y) (ev k y1))
	    (= (ev m z) (ev k z1))
	    (= (space x1) spacezero)
	    (= (space y1) spacezero))))

(defparameter *B2-6*
  (problem 
   :name "B2-6"
   :doc "x1,y,z1 are distinct"
   :goal 
   '(and (not (= x1 y1)) (not (= y1 z1)) (not (= z1 x1)) )
   :axioms ()
   :assumptions (append *properties-of-z* *properties-of-x1y1z1*)
   :sub-problems ()))
(eval-when (:execute) (semi-prove *B2-6* :verbose t :visualize t))

(defparameter *AxFd-w-existence*
  (check-syntax-s
   '(forall ((?x :sort Q4) (?y :sort Q4) (?z :sort Q4))
     (implies (and (= (space ?x) spacezero) (= (space ?y) spacezero)
	       (not (= ?x ?y)) (not (= ?y ?z)) (not (= ?z ?x)))
      (exists ((?w :sort Q4))
       (and (EquivSTDistance ?z ?w)
	    (EquivSTDistance ?w ?x)
	    (EquivSTDistance ?w ?y)))))))

(defparameter *B2-7*
  (problem 
   :name "B2-7"
   :doc "there is a w such that z-w and w-x and w-y are of slope 1"
   :goal 
   '(exists ((?w :sort Q4))
      
     (and 
      (EquivSTDistance z1 ?w)
      (EquivSTDistance ?w x1)
      (EquivSTDistance ?w y1)))   
   :axioms ()
   :assumptions (append  *properties-of-x1y1z1* (list *AxFd-w-existence*))
   :sub-problems (list *B2-6*)))
(eval-when (:execute) (semi-prove *B2-7* :verbose t :visualize t))

(defparameter *properties-of-w1*
  (check-syntax-s   
   '(and 
    (EquivSTDistance z1 w1)
    (EquivSTDistance w1 x1)
    (EquivSTDistance w1 y1))))

(defparameter *geometic-sanity-check*
  (problem :goal 'false
	   :assumptions *branch-2-geometric-lemmas*))
(eval-when (:execute) (semi-prove *geometic-sanity-check* :verbose t :visualize t))

(defparameter *B2-7.1*
  (problem 
   :name "s5a"
   :doc "k sees p1 at x1 and w1"
   :goal '(and 
	   (exists ((?p :sort Body)) (and (Ph ?p) (W k ?p x1)  (W k ?p w1))))
   :axioms (list *AxPh*)
   :assumptions (append   *branch-2-assumptions* (list  *properties-of-w1*))))
(eval-when (:execute) (semi-prove *B2-7.1* :verbose t :visualize t))

(defparameter *B2-7.2*
  (problem 
   :name "s5b"
   :doc "k sees p2 at y1 and w1"

   :goal '(and 
	   (exists ((?p :sort Body)) (and (Ph ?p) (W k ?p y1)  (W k ?p w1))))
   :axioms (list *AxPh*)
   :assumptions (append   *branch-2-assumptions* (list  *properties-of-w1*))))
(eval-when (:execute) (semi-prove *B2-7.2* :verbose t :visualize t))


(defparameter *B2-7.3*
  (problem 
   :name "s5c"
   :doc "k sees p3 at z1 and w1"

   :goal '(and 
	   (exists ((?p :sort Body)) (and (Ph ?p) (W k ?p z1)  (W k ?p w1))))
   :axioms (list *AxPh*)
   :assumptions (append   *branch-2-assumptions* (list  *properties-of-w1*))))
(eval-when (:execute) (semi-prove *B2-7.3* :verbose t :visualize t))

(defparameter *B2.7.1.2.3-skolemized*
  (check-syntax
   (list  '(and (Ph p1) (W k p1 x1)  (W k p1 w1))
	  '(and (Ph p2) (W k p2 y1)  (W k p2 w1))
	  '(and (Ph p3) (W k p3 z1)  (W k p3 w1)))))

(defparameter *B2-8*
  (problem 
   :name "s5"
   :doc "there is a w such that z-w and w-x and w-y are of slope 1"
   :goal 
   '(and (W m p1 x) (W m p2 y) (W m p3 z))   
   :axioms *axioms*
   :assumptions (append *properties-of-x1y1z1*  *B2.7.1.2.3-skolemized*)
   :sub-problems  nil))
(eval-when (:execute) (semi-prove *B2-8* :verbose t :visualize t))

(defparameter *B2-9*
  (problem 
   :name "s4"
   :doc "there is a w such that z-w and w-x and w-y are of slope 1"
   :goal 
   '(exists ((?w :sort Q4)) (= (ev m  ?w) (ev k w1)))   
   :axioms (list *def-event* *AxEv* *AxPh*)
   :assumptions  *branch-2-assumptions*
   :sub-problems  nil))
(eval-when (:execute) (semi-prove *B2-9* :verbose t :visualize t))

(defparameter *w-defined*
  (check-syntax-s
    '(= (ev m  w) (ev k w1))))


(defparameter *B2-10a*
  (problem 
   :name "s3a"
   :doc "m sees p1 at x and w"
   :goal 
   '(exists ((?p :sort Body) ;(?p2 :sort Body) (?p3 :sort Body)
	     )
     (and (Ph ?p)
      (W m ?p x) ; (W m ?p2 y) (W m ?p3 z)
      (W m ?p w) ;(W m ?p2 w) (W m ?p3 w)
      ))   
   :axioms (list *def-event* *AxEv* *AxPh*)
   :assumptions  (append (list *w-defined* ) *properties-of-x1y1z1* *branch-2-assumptions*)
   :sub-problems  (list *B2-7.1*)))
(eval-when (:execute) (semi-prove *B2-10a* :verbose t :visualize t))

(defparameter *B2-10b*
  (problem 
   :name "s3b"
   :doc "m sees p1 at y and w"
   :goal 
   '(exists ((?p :sort Body) ;(?p2 :sort Body) (?p3 :sort Body)
	     )
     (and (Ph ?p)
      (W m ?p y) ; (W m ?p2 y) (W m ?p3 z)
      (W m ?p w) ;(W m ?p2 w) (W m ?p3 w)
      ))   
   :axioms (list *def-event* *AxEv* *AxPh*)
   :assumptions  (append (list *w-defined* ) *properties-of-x1y1z1* *branch-2-assumptions*)
   :sub-problems  (list *B2-7.2*)))
(eval-when (:execute) (semi-prove *B2-10b* :verbose t :visualize t))

(defparameter *B2-10c*
  (problem 
   :name "s3c"
   :doc "m sees p1 at z and w"
   :goal 
   '(exists ((?p :sort Body) ;(?p2 :sort Body) (?p3 :sort Body)
	     )
     (and (Ph ?p)
      (W m ?p z) ; (W m ?p2 y) (W m ?p3 z)
      (W m ?p w) ;(W m ?p2 w) (W m ?p3 w)
      ))   
   :axioms (list *def-event* *AxEv* *AxPh*)
   :assumptions  (append (list *w-defined* ) *properties-of-x1y1z1* *branch-2-assumptions*)
   :sub-problems  (list *B2-7.3*)))
(eval-when (:execute) (semi-prove *B2-10c* :verbose t :visualize t))


(defparameter *B2-11*
  (problem 
   :name "s2"
   :doc "there is a w such that z-w and w-x and w-y are of slope 1"
   :goal 
   '(and  
     (EquivSTDistance x z)  (EquivSTDistance x w)  (EquivSTDistance w z)  (EquivSTDistance w y))   
   :axioms (list *def-event* *AxEv* *AxPh*)
   :assumptions  (append (list *branch-2-properties-of-z* *w-defined* ) *branch-2-assumptions*)
   :sub-problems  (list *B2-10a* *B2-10b* *B2-10c*)))
(eval-when (:execute) (semi-prove *B2-11* :verbose t :visualize t))


(defparameter *B2-11-ge*
  (problem 
   :name "s1"
   :doc "there is a w such that z-w and w-x and w-y are of slope 1"
   :goal 
   '(not
 (= (slopel (line w y)) (slopel (line x z))))   
   :axioms ()
   :assumptions  (append *branch-2-geometric-lemmas* (list '(not (EquivSTDistance x y))))
   :sub-problems  (list *B2-11* *branch-2-final-geometric-3*)))
(eval-when (:execute) (semi-prove *B2-11-ge* :verbose t :visualize t))

(defparameter *Branch-2-final*
  (problem :goal 'false
	   :name "B2"
	   :doc "Final b2"
	   :assumptions (append *branch-2-geometric-lemmas* ; (list '(not (= (slopel (line w y)) (slopel (line x z)))))
				)
	   :sub-problems (list *B2-11*  *B2-11-ge*)))
(eval-when (:execute) (semi-prove *Branch-2-final* :verbose t :visualize t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;; Branch 3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defparameter *branch-3-assumptions*
  (list '(IOb m) 
	'(IOb k)
	'(not (= x y)) 
	'(W m k x)
	'(W m k y)
	'(EquivSTDistance x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;; FIELD LEMMAS ;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defparameter *branch-3-field-lemmas*
  (list
   ;; 
   '(forall ((?x :sort Q4) (?y :sort Q4))
     (implies   
      (and (= (c1 ?x) (c1 ?y)) (= (c2 ?x) (c2 ?y)) (= (c3 ?x) (c3 ?y)))
      (= zero (m3 (minus-3 (space ?x) (space ?y))))))
   '(forall ((?x :sort Qs) (?y :sort Qs))
     (implies (= zero (m1 (minus-s ?x ?y)))
      (= ?x ?y)))
   '(forall ((?x :sort Q4) (?y :sort Q4))
     (implies (and 
	       (= (c1 ?x) (c1 ?y))
	       (= (c2 ?x) (c2 ?y)) 
	       (= (c3 ?x) (c3 ?y))
	       (= (time ?x) (time ?y)))
      (= ?x ?y)))))
(defparameter *branch-3-field-p-1*
  (problem 
   :name "t4"
   :doc "If two points are spatially at the origin, their spatial distance is zero."
   :goal '(forall ((?x :sort Q4) (?y :sort Q4))
	   (implies 
	    (and 
	     (and (= (c1 ?x) zero) (= (c2 ?x) zero) (= (c3 ?x) zero))
	     (and (= (c1 ?y) zero) (= (c2 ?y) zero) (= (c3 ?y) zero)))
	    (= zero (m3 (minus-3 (space ?x) (space ?y))))))
   :axioms nil
   :assumptions *branch-3-field-lemmas*))

(defparameter *branch-3-field-p-2*
  (problem 
   :name "t3"
   :doc "If two points are spatially at the origin and their temporal and spatial distances are the same, their time components are the same."
   :goal '(forall ((?x :sort Q4) (?y :sort Q4))
	   (implies 
	    (and 
	     (and (= (c1 ?x) zero) (= (c2 ?x) zero) (= (c3 ?x) zero))
	     (and (= (c1 ?y) zero) (= (c2 ?y) zero) (= (c3 ?y) zero))
	     (EquivSTDistance ?x ?y))
	    (= (time ?x) (time ?y))))
   :axioms (list *EquivSTDistance-x-y*)
   :assumptions *branch-3-field-lemmas*
   :sub-problems (list *branch-3-field-p-1*)))

(defparameter *branch-3-field-p-3*
  (problem 
   :name "t3"
   :doc "If two points are spatially at the origin and their temporal and spatial distances are the same, they are equal"
   :goal '(forall ((?x :sort Q4) (?y :sort Q4))
	   (implies 
	    (and 
	     (and (= (c1 ?x) zero) (= (c2 ?x) zero) (= (c3 ?x) zero))
	     (and (= (c1 ?y) zero) (= (c2 ?y) zero) (= (c3 ?y) zero))
	   ;  (EquivSTDistance ?x ?y)
	     )
	    (and 
	     (= (c1 ?x) (c1 ?y))
	     (= (c2 ?x) (c2 ?y))
	     (= (c3 ?x) (c3 ?y)))))
   :axioms (list *EquivSTDistance-x-y*)
   :assumptions *branch-3-field-lemmas*))
(eval-when (:execute) (semi-prove *branch-3-field-p-3* :visualize t
				  )) 


(defparameter *branch-3-field-p-4*
  (problem 
   :name "t2"
   :doc "If two points are spatially at the origin and their temporal and spatial distances are the same, they are equal"
   :goal '(forall ((?x :sort Q4) (?y :sort Q4))
	   (implies 
	    (and 
	     (and (= (c1 ?x) zero) (= (c2 ?x) zero) (= (c3 ?x) zero))
	     (and (= (c1 ?y) zero) (= (c2 ?y) zero) (= (c3 ?y) zero))
	     (EquivSTDistance ?x ?y))
	    (= ?x ?y)))
   :axioms nil
   :assumptions (list   '(forall ((?x :sort Q4) (?y :sort Q4))
			  (implies (and 
				    (= (c1 ?x) (c1 ?y))
				    (= (c2 ?x) (c2 ?y)) 
				    (= (c3 ?x) (c3 ?y))
				    (= (time ?x) (time ?y)))
			   (= ?x ?y))))
   :sub-problems (list *branch-3-field-p-2* ;*branch-3-field-p-3*
		       )))
(eval-when (:execute) (semi-prove *branch-3-field-p-4* :visualize t
				  )) 

(defparameter *branch-3-1*
  (problem 
   :name "branch-3-1"
   :goal 
   '(exists ((?p :sort Body))
	   (and (Ph ?p) (In (ev m x) ?p) (In (ev m y) ?p)))
   :axioms (list *AxPh* *def-event* )
   :assumptions *branch-3-assumptions*))


(defparameter *branch-3-2*
  (problem 
   :name "branch-3-2"
   :goal 
   '(not  (= (ev m x) (ev m y)))
   :axioms (list *AxPh* *def-event* *Theorem-Neat*)
   :assumptions *branch-3-assumptions*))

(defparameter *branch-3-a*
  (problem 
   :name "B3-a"
   :doc "k observes (ev m x) and (ev m y) at two points"
   :goal '(exists ((?x1 :sort Q4) (?y1 :sort Q4))
	   (and 
	    (= (ev m x) (ev k ?x1))
	    (= (ev m y) (ev k ?y1))))
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
   :assumptions *branch-3-assumptions*))


(defparameter *branch-3-b*
  (problem 
   :name "B3-a"
   :doc "k observes (ev m x) and (ev m y) at two points"
   :goal '(forall ((?x1 :sort Q4) (?y1 :sort Q4))
	   (implies
	    (and 
	     (= (ev m x) (ev k ?x1))
	     (= (ev m y) (ev k ?y1)))
	    (not (= ?x1 ?y1))))
   :axioms (list  *AxEv*  *def-event*  *Theorem-Neat*)
   :assumptions *branch-3-assumptions*
   :sub-problems (list *branch-3-a*)))

(defparameter *branch-3-all*
  (problem 
   :name "t1"
   :doc "k sees itself at x1 and y1 "
   :goal '(forall ((?m :sort Body)
		   (?k :sort Body)
		   (?x :sort Q4)
		   (?y :sort Q4))
	   (implies  (and (IOb ?m) 
		      (IOb ?k)
		      (not (= ?x ?y)) 
		      (W ?m ?k ?x)
		      (W ?m ?k ?y)
		      (EquivSTDistance ?x ?y))
	    (exists ((?x1 :sort Q4) (?y1 :sort Q4))
	     (and 
	      (not (= ?x1 ?y1))
	      (= (ev ?m ?x) (ev ?k ?x1))
	      (= (ev ?m ?y) (ev ?k ?y1))
	      (and (= (c1 ?x1) zero) (= (c2 ?x1) zero) (= (c3 ?x1) zero))
	      (and (= (c1 ?y1) zero) (= (c2 ?y1) zero) (= (c3 ?y1) zero))
	      (EquivSTDistance ?x1 ?y1)))))
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)))


(eval-when (:execute) (semi-prove *branch-3-all* :visualize t
				  )) 

(defparameter *branch-3-all-1*
  (problem 
   :name "B3-A1"
   :doc "If m sees k at x, k sees k at x1"
   :goal '(exists ((?x1 :sort Q4))
	   (and 
	    (= (ev m x) (ev k ?x1))
	    (and (= (c1 ?x1) zero) (= (c2 ?x1) zero) (= (c3 ?x1) zero))))
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
   :assumptions *branch-3-assumptions*))

(defparameter *branch-3-all-2*
  (problem 
   :name "B3-A2"
   :doc "If m sees k at y, k sees k at y1"
   :goal '(exists ((?y1 :sort Q4) )
	   (and 
	    (= (ev m y) (ev k ?y1))
	    (and (= (c1 ?y1) zero) (= (c2 ?y1) zero) (= (c3 ?y1) zero))))
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
   :assumptions *branch-3-assumptions*))

(defparameter *branch-3-all-3*
  (problem 
   :name "B3-A3"
   :doc "x1 not equal to y1"
   :goal '(exists ((?x1 :sort Q4)(?y1 :sort Q4) )
	   (and 
	    (not (= ?x1 ?y1))
	    (= (ev m x) (ev k ?x1))
	    (= (ev m y) (ev k ?y1))))
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
   :assumptions *branch-3-assumptions*))
(defparameter *branch-3-all-4*
  (problem 
   :name "B3-A4"
   :doc "x1 and y1 are on the light cone"
   :goal '(exists ((?x1 :sort Q4)(?y1 :sort Q4) )
	   (and 
	    (= (ev m x) (ev k ?x1))
	    (= (ev m y) (ev k ?y1))
	    (EquivSTDistance ?x1 ?y1)))
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
   :assumptions *branch-3-assumptions*))

(defparameter *branch-3-conflict-modular*
  (problem 
   :name "BT-1"
   :doc "Deriving a contradiction for Case 3"
   :goal 'false
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
   :assumptions *branch-3-assumptions*
   :sub-problems (list  *branch-3-all-1* *branch-3-all-2* *branch-3-all-3* *branch-3-all-4* *branch-3-field-p-4*)))
(eval-when (:execute) (semi-prove *branch-2-final-geometric-1* :visualize t )) 

(defparameter *branch-3-conflict-monolithic*
  (problem 
   :name "B3"
   :doc "Reductio"
   :goal 'false
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
   :assumptions *branch-3-assumptions*
   :sub-problems (list  *branch-3-all* *branch-3-field-p-4*)))
(eval-when (:execute) (semi-prove *branch-3-conflict-monolithic* :visualize t )) 


(defparameter *branch-k-see-k-at-distinct-points*
  (problem 
   :name "BT-2"
   :doc "k observes k at distinct points"
   :goal '(exists ((?x1 :sort Q4) (?y1 :sort Q4))
	   (and 
	    (= (ev m x) (ev k ?x1))
	    (= (ev m y) (ev k ?y1))
	    (not (= ?x ?y))))
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
   :assumptions *branch-3-assumptions* ))

(defparameter *branch-k-see-k-on-the-light-cone*
  (problem 
   :name "BT-2"
   :doc "k observes k at distinct points"
   :goal '(exists ((?x1 :sort Q4) (?y1 :sort Q4))
	   (and 
	    (= (ev m x) (ev k ?x1))
	    (= (ev m y) (ev k ?y1))
	    (EquivSTDistance ?x1 ?y1)))
   :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
   :assumptions *branch-3-assumptions*))
;; (defparameter *branch-3-final*
;;   (problem 
;;    :name "branch-3-3"
;;    :doc "k observ"
;;    :goal '(exists ((?x1 :sort Q4) (?y1 :sort Q4))
;; 	   (and 
;; 	    (= ?x1 ?y1)
;; 	    (= (ev m x) (ev k ?x1))
;; 	    (= (ev m y) (ev k ?y1))
;; 	    (and (= (c1 ?x1) zero) (= (c2 ?x1) zero) (= (c3 ?x1) zero))
;; 	    (and (= (c1 ?y1) zero) (= (c2 ?y1) zero) (= (c3 ?y1) zero))
;; 	    (EquivSTDistance ?x1 ?y1)))
;;    :axioms (list *AxPh* *AxEv*  *AxSf* *def-event*  *EquivSTDistance-x-y* *Theorem-Neat*)
;;    :assumptions *branch-3-assumptions*
;;    :sub-problems (list *branch-k-see-k-at-origin* *branch-k-see-k-at-distinct-points* *branch-3-field-p-4*) ))


;; This is a sanity check
(defparameter *quick-sanity-check*
  (problem 
   :name "quick-sanity-check"
   :goal 
   '(not  (= x x))
   :assumptions *branch-3-assumptions*))

