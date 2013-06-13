
(in-package :semi-prover-tests)

(defparameter *problem-1*
  (problem :goal '(or  P (not P))))
(defparameter *problem-2*
  (problem :goal '(and P (not P))))



(defparameter *passing-tests*
  (list *problem-1*))

(defparameter *failing-tests*
  (list *problem-2*))


(defun verbose-proving (problem should-pass?)
  (let ((answer
	 (if should-pass?
	     (semi-prover:semi-prove problem)
	     (handler-case (semi-prover:semi-prove problem)
	       (error () t)
	       (no-error-clause () nil))))) 
    (format t "========TEST CASE=============~%")
    
    (print problem)
    (format t "~%_______________________ ~%")
    (format t "Expectation (shoud pass?): ~a~%" should-pass? )
    (format t "Result                   : ~a~%" (and should-pass? (not (null answer))))
    (format t "=====================~%")
    t))

(defun run-batch (problems should-pass?)
 (every (complement #'null) 
	(mapcar (lambda (problem) 
		  (verbose-proving problem should-pass?)) problems)))
(defun run-all-tests ()
  (if (and (run-batch *passing-tests* t)
	   (run-batch *failing-tests* nil))
      (format t "~%ALL TESTS PASSED.")
      (format t "~%SOME TESTS FAILED.")))