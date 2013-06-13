(in-package #:semi-prover)

(defparameter *axioms* nil)
(defparameter *axiom-names* nil)

(defparameter !logic-declarations! (lambda ()))

(defparameter *proof-cache-location* "/Users/Naveen/work/logicphysics/proof-cache-snark")
(defparameter *temp-dot-file* "/Users/Naveen/work/logicphysics/temp-dot-file.dot")


(defun snark-deverbose ()
 (snark:print-options-when-starting  nil)
  (snark:print-agenda-when-finished nil)
  (snark:print-clocks-when-finished nil)
  (snark:print-final-rows nil)
  (snark:print-symbol-table-warnings nil)
  (snark:print-summary-when-finished nil)
  (snark:print-row-answers nil)
  (snark:print-row-goals nil) 
  (snark:print-rows-when-derived nil)
  (snark:print-row-reasons nil)
  (snark:print-row-partitions nil)
  (snark:print-rows-prettily nil)
  (snark:print-rows :min 0 :max 0))


(defun setup-snark (&optional  (verbose t))
  (snark:initialize :verbose  verbose)
  (if (not verbose) (snark-deverbose))
  (snark:assert-supported t)
  (snark:assume-supported t)
  (snark:prove-supported t)
  (snark:use-factoring t)
  (snark:use-equality-factoring t)
  (snark:rewrite-answers t)
  (snark:use-resolution t)
  (snark:use-hyperresolution t)
  (snark:use-paramodulation t)
  (snark:allow-skolem-symbols-in-answers nil)
  (funcall  !logic-declarations!))
(defun get-param (key param) (cdr (assoc key param)))


(defclass problem ()
    ((name :accessor name 
	   :initform (princ-to-string (gensym "Problem_"))
	   :initarg :name 
	   :type string)
     (documentation :accessor doc 
		    :initform ""
		    :initarg :doc 
		    :type string)
     (goal :accessor goal 
	   :initform (error "Need a goal for creating a problem.")
	   :initarg :goal :type list)
     (axioms :accessor axioms 
	     :initform nil
	     :initarg :axioms
	     :type list)
     (assumptions :accessor assumptions
		  :initform nil
		  :initarg :assumptions
		  :type list)
     (justification :accessor justification
		    :initform :semi
		    :initarg :justification)
     (sub-problems :accessor sub-problems
		   :initform ()
		   :initarg :sub-problems
		   :type list)))

(defclass proof ()
  ((rows :accessor proof-rows :initarg :rows :type list)
   (reasons :accessor proof-reasons :initarg :reasons :type list)))

(defmethod print-object ((p proof) stream)
  (format stream "[Rows ")
  (pprint (proof-rows p) stream)
  (format stream "]  ~%==========~%")
  (format stream "[Reasons ")
  (pprint (proof-reasons p) stream)
  (format stream "]"))

(defun problem (&key 
		goal  
		name
		(axioms 
		 (if (boundp '*axioms*)
		     *axioms* 
		     nil))
		(assumptions nil)
		(justification :semi)
		(sub-problems nil)
		(doc ""))
  (cl:assert (subsetp axioms *axioms* :test #'equalp))
  (make-instance 
   'problem 
   :name name 
   :goal (check-syntax-s goal) 
   :axioms axioms :assumptions (check-syntax assumptions) 
   :sub-problems sub-problems :doc doc
   :justification justification))


(defun problem-hash (problem)
  (concatenate 'string  
	       (princ-to-string (name problem))
	       (princ-to-string (goal problem))
	       (princ-to-string (axioms problem))
	       (princ-to-string (assumptions problem))
	       (princ-to-string (mapcar #'problem-hash (sub-problems problem)))))
 


(defparameter *proof-cache* (make-hash-table :test 'equalp))
;(setf *proof-cache* (cl-store:restore *proof-cache-location*))

(defun clear-proof-cache! () (setf *proof-cache*(make-hash-table :test 'equalp)))


(defun fetch-from-cache (problem) 
  (gethash 
   (problem-hash problem) 
   *proof-cache*))

(defun put-into-cache (problem proof) 
  (setf (gethash (problem-hash problem) *proof-cache*) proof)
  (cl-store:store *proof-cache* *proof-cache-location*)
  proof)

(defun snark-prove-simple (problem &optional (verbose t))
  (setup-snark verbose)
  (mapcar #'snark::assert (axioms problem))
  (mapcar #'snark::assert (assumptions problem))
  (let ((result (snark:prove (goal problem))))
    (if (eq result :PROOF-FOUND)
	t
	(error "Snark could not prove ~a from ~a" (goal problem) (axioms problem)))))

(defun semi-prove (problem &key (verbose t) (visualize nil)) 
  (let ((solution (fetch-from-cache problem)))
    (if solution 
	(progn (if visualize (visualize problem)) solution) 
	(let ((result
	      (if (null (sub-problems problem))
		  (snark-prove-simple problem verbose)
		  (if (mapcar (lambda (sub) 
				(semi-prove sub :verbose verbose :visualize nil)) 
			      (sub-problems problem))
		      (snark-prove-simple
		       (make-instance 'problem 
				      :goal (goal problem)
				      :axioms (append 
					       (assumptions problem)
					       (axioms problem) 
					       (mapcar #'goal (sub-problems problem))))
		       verbose)))))
	  (if result 
	      (progn (put-into-cache
		      problem
		      (make-instance 'proof
				     :rows (snark:row-ancestry (snark:proof))
				     :reasons (mapcar 'snark:row-reason (snark:row-ancestry (snark:proof)))))
		     (if visualize (visualize problem))
		     result))))))


(defun check-syntax-s (sent)
  (setup-snark nil)
  (snark::assert sent)
  sent)
(defun check-syntax (sents)
  (setup-snark nil)
  (mapcar #'snark::assert sents)
  sents)

(defmethod print-object ((obj problem) out)
  (print-unreadable-object (obj out :type t)
    (format out "~%---------[Name: ~a]-------------~%" (name obj))
    (format out "GOAL:~% ~a" (goal obj))
    (if (axioms obj)
	(progn     
	  (format out "~%--------------------------~%")
	  (format out "AXIOMS: ~%")
	  (format out "~{  ~A~^~%  ~}" (axioms obj))
	  (format out "--------------------------")))
    (if (assumptions obj)
	(progn     
	  (format out "~%--------------------------~%")
	  (format out "ASSUMPTIONS: ~%")
	  (format out "~{  ~A~^~%  ~}" (assumptions obj))
	  (format out "--------------------------")))
    (if (sub-problems obj)
	(progn     
	  (format out "~%SUB PROBLEMS ~% ")
	  (mapcar #'print (sub-problems obj))))
    (format out "~%--------------------------~%")))


(defclass problem-graph ()
  ((top :accessor problem-graph-top :initarg :top )
   (graph :accessor problem-graph-graph :initarg :graph)))


(defun head (expression) (first expression))

(defun args (expression) (rest expression))
(defparameter *signature-table*
  '(time Ph IOb Ob slopel line on-line plane on-plane c1 c2 c2 c3 W ev light-speed EquivSTDistance space))


(defun de-lispify (exp)
  (if (symbolp exp)
      (symbol-name exp)
      (if (member (head exp) *signature-table* :test #'(lambda (x y) 
							 (and 
							  (symbolp x) (symbolp y) 
							  (equalp (symbol-name x) (symbol-name y)))))
	  (concatenate 'string 
		       (symbol-name (head exp)) 
		      "(" (format nil "~{~a~^COMMA~}"  (mapcar #'de-lispify (args exp))) ")")
	  (concatenate 'string "("
		       (format nil "~{~a~^ ~}" (mapcar #'de-lispify exp)) ")"))))

(de-lispify '(forall ((x s)) (if a a)))
(member 'c13 *signature-table*)

(defun preprocess-forumula (exp)
  (let ((local_exp exp))
        (mapcar (lambda (sub) 
	      (setf local_exp (subst (second sub) (first sub) local_exp :test #'equalp))
	   ;   (format t "~%now ~a " local_exp)
	      ) 
	    '((snark::and logic!_!and)
	      (snark::or logic!_!or)
	      (snark::implies logic!_!implies)
	      (snark::iff logic!_!iff)
	      (snark::forall logic!_!forall)
	      (snark::exists logic!_!exists)
	      (snark::not logic!_!not)))
	(setf local_exp (prefix->infix local_exp '(logic!_!or logic!_!and logic!_!implies logic!_!iff = c1 light-speed)))
local_exp))
(preprocess-forumula  '(implies (or a b) b))

(defun gen-node-id ()  (substitute-if #\_ (complement #'alphanumericp) (symbol-name  (gensym "NODE_"))))
(defun sym= (x y) (and (symbolp x) (symbolp y) (equalp (symbol-name x) (symbol-name y))))
(defun problem-to-dot-int (problem &optional (top-node-id (gen-node-id)))
  (let ((current-level 
	 (concatenate 'string 
		      ;; (reduce 
		      ;;  (lambda (x y) (concatenate 'string x  y))
		      ;;  (mapcar  (lambda (assum)
		      ;; 		  (let ((name-assum (gen-node-id)))
		      ;; 		    (format nil "~a[texmode=\"math\", label=\" ~a\"]; ~a -> ~a; ~%" name-assum (subscript (string-downcase (let ((*print-pretty* t))
		      ;; 							 (princ-to-string (read-from-string (de-lispify
		      ;; 											     (preprocess-forumula assum)))))))name-assum top-node-id)))
		      ;; 		(assumptions problem)))
		      (format nil "~a[texmode=\"math\",label=\"\\\\\textbf{\\\\\textsf{\\\\\colorbox{red}{\\\\\textcolor{white}{~a}}}}\",fixedsize=\"true\",shape=box,color=\"~a\"];~%"
				       top-node-id
				       (name problem) 
				    ;;   (if (sym= (goal problem) 'false)
				       ;; 	   "Contradiction"
				       ;; 	   (subscript (string-downcase (let ((*print-pretty* t))
				       ;; 					 (princ-to-string (read-from-string (de-lispify
				       ;; 									     (preprocess-forumula (goal problem)))))))))
				       ;; (doc problem)	
				       ;; (if (axioms problem) (format nil "[~{~a~^, ~}]"	(mapcar (lambda (a) (get-param a *axiom-names*)) (axioms problem))) "")
				;	(string-downcase (format  nil "~{  ~A~^|  ~}"  (assumptions problem)))
				       (if (sym= (goal problem) 'false) "red" "grey")))))
    (if (null (sub-problems problem))
	current-level
	(concatenate 'string  
		     current-level
		     (reduce (lambda (p q) (concatenate 'string p q))
			     (mapcar (lambda (p) 
				       (let ((id (gen-node-id)))
					 (concatenate 'string
						  (format nil "~a->~a;~%" top-node-id id)
						     (problem-to-dot-int p id))))
				     (sub-problems problem)))))))

(reduce (lambda (x y) (concatenate 'string x y)) (list "a" "b" "c"))

(defun problem-to-dot (problem)
  (format nil "digraph {
  ~% ~a   ~%}"  (problem-to-dot-int problem)
 ;; (reduce (lambda (x y) (concatenate 'string x y))
 ;; 	(mapcar (lambda (name ax) 
 ;; 		  (format nil " ~a[texmode=\"verbatim\", label=\"~a\",fixedsize=\"false\",shape=doublecircle,color=\"green\"];"  name name)) ;
 ;; 			  ;; (subscript (string-downcase (let ((*print-pretty* t))
 ;; 			  ;; 				(princ-to-string (read-from-string (de-lispify
 ;; 			  ;; 								    (preprocess-forumula ax)))))))))
		
 ;; 		(mapcar (lambda (a) (get-param a *axiom-names*))   *axioms*)
 ;; 		*axioms*))
 ))
(defun subscript (str) (cl-ppcre::regex-replace-all "\\d" str "\\_\\&"))
(subscript "(logic!_!forall ((?x2 sort q_4) (?y sort q4))  ((((c1 (?x) = zero) logic!_!and (c2 (?x) = zero) logic!_!and (c3 (?x) = zero))
   logic!_!and
   ((c1 (?y) = zero) logic!_!and (c2 (?y) = zero) logic!_!and (c3 (?y) = zero))
   logic!_!and (equiv_space_time_distance ?x ?y))
  logic!_!implies
  ((c1 (?x) = c1 (?y)) logic!_!and (c2 (?x) = c2 (?y)) logic!_!and
   (c3 (?x) = c3 (?y)))))")

(defun visualize (problem)
  (with-open-file (str *temp-dot-file*
		       :direction :output
		       :if-exists :supersede
		       :if-does-not-exist :create)
    (format str  (problem-to-dot problem) ))
  (trivial-shell:shell-command "/Users/Naveen/work/logicphysics/substitute_unicode.sh")
  (trivial-shell:shell-command (format nil "dot -Txdot -O ~a" *temp-dot-file*))
  (with-open-file (out "/Users/Naveen/work/logicphysics/latex/test.tex" :direction :output :if-exists :supersede)
    (format out 
	    (trivial-shell:shell-command  
	     "dot2tex -c --texmode math   --margin 6pt /Users/Naveen/work/logicphysics/temp-dot-file.dot.xdot ")))
  (trivial-shell:shell-command "cd /Users/Naveen/work/logicphysics/latex ; pdflatex /Users/Naveen/work/logicphysics/latex/test.tex")
  (trivial-shell:shell-command (format nil "open /Users/Naveen/work/logicphysics/latex/test.pdf -F")))

(defun display-table (exp)
  (case 'exp
    ('and '&) 
    ('or 'V)
    ('implies '=>)
    ('iff '<=>)
    ('forall )))

(defun to-prefix (expression)
  ())



(defun problem-to-dot-int2 (problem &optional (top-node-id (gen-node-id)))
  (let ((current-level 
	 (concatenate 'string 
		      (format nil " \\colorbox{red}{{\\color{white}\\textbf{\\textsf{~a}}}} $~a$ \\\\  \\colorbox{gray}{{\\color{white}\\textbf{\\textsf{~a}}}} \\colorbox{white}{{\\color{gray}{\\textsf{~a}}}} ~% "
				       (name problem) 
				       (if (sym= (goal problem) 'false)
				       	   "Contradiction"
				       	   (subscript (string-downcase (let ((*print-pretty* t))
				       					 (princ-to-string (read-from-string (de-lispify
				       									     (preprocess-forumula (goal problem)))))))))
				       (doc problem)	
				       (format nil "[~{~a~^, ~}]"	(mapcar (lambda (a) (get-param a *axiom-names*)) (axioms problem)))			;(string-downcase (format  nil "~{  ~A~^|  ~}"  (assumptions problem)))
				     ;(if (sym= (goal problem) 'false) "red" "grey")
				     ))))
    (if (null (sub-problems problem))
	current-level
	(concatenate 'string  
		     current-level
		     "
\\begin{enumerate}"
		     (reduce (lambda (p q) (concatenate 'string p q))
			     (mapcar (lambda (p) 
				       (let ((id (gen-node-id)))
					 (concatenate 'string
						   ;(format nil "~a->~a[weight=2000, len=0];~%" top-node-id id)
						 "\\item "    (problem-to-dot-int2 p id) "~%" )))
				     (sub-problems problem)))
		     "\\end{enumerate}"))))

(defun problem-to-dot2 (problem)
  (format nil  "\\documentclass[a4paper,portrait]{article} \\usepackage{enumitem}
\\usepackage{color} \\usepackage{fullpage} \\usepackage[usenames,dvipsnames]{xcolor}


\\begin{document}\\begin{scriptsize}~a \\end{scriptsize}\\end{document}" (problem-to-dot-int2 problem)
 ))
(defun visualize2 (problem)
  (with-open-file (str "/Users/Naveen/work/logicphysics/latex/test.tex"
		       :direction :output
		       :if-exists :supersede
		       :if-does-not-exist :create)
    (format str  (problem-to-dot2 problem) ))
  (trivial-shell:shell-command "/Users/Naveen/work/logicphysics/substitute_unicode_tex.sh")
 
  (trivial-shell:shell-command "cd /Users/Naveen/work/logicphysics/latex ; pdflatex /Users/Naveen/work/logicphysics/latex/test.tex")
  (trivial-shell:shell-command (format nil "open /Users/Naveen/work/logicphysics/latex/test.pdf -F")))
