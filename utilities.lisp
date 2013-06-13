
(in-package #:utilities)

(eval-when (:compile-toplevel :load-toplevel :execute)

(defun to-list (x)
  "* Syntax:
to-list list-designator => designated-list
* Description:
to-list returns the list designated by the list designator."
  (if (listp x) x
    (list x)))

(defun singletonp (list)
  "* Syntax:
singletonp list => generalized-boolean
* Arguments and Values:
- list---a proper list
* Description:
singletonp returns true if list contains exactly one element.  The
length of the list is not computed."
  (and (not (endp list))
       (endp (rest list))))

(defmacro with-gensyms (vars &body body)
  "* Syntax:
with-gensyms (var*) form* => result*
* Arguments and Values:
- var---a variable
- form---a form
- result---values produced by forms
* Description:
with-gensyms binds each var to a fresh symbol with the same name
\(created with make-symbol\) and evaluates forms within the scope of
the binding.
* Examples:
;;; (with-gensyms (x y z)
;;;   (list x y z))
;;; => (#:X #:Y #:Z)
"
  (flet ((gsym (x) `(,x (make-symbol ,(symbol-name x)))))
    `(let (,@(mapcar #'gsym vars))
       ,@body)))

(defun treeduce (function tree init)
  "* Syntax:
treeduce function tree init => value
* Arguments and Values:
- function---a function of two arguments
- tree---a tree
- init---an object
* Description:
treeduce computes the left associative reduction of function over the
leaves of the tree.  init is treated as the leftmost element, and it
returned, unmodified, if tree is nil.
* Examples:
;;; (flet ((xcons (cdr car) (cons car cdr)))
;;;   (treeduce #'xcons '(1 (2 3) (4 . 5)) '()))
;;; => (5 4 3 2 1)
"
  (cond
   ((null tree) init)
   ((atom tree) (funcall function init tree))
   ((treeduce function
              (cdr tree)
              (treeduce function
                        (car tree)
                        init)))))

(defun treecompose (function tree K)
  "* Syntax:
treecompose function tree continuation => result* 
* Arguments and Values:
- function---a function of two arguments
- tree---a tree
- continuation---a function of zero arguments
- results---produced by continuation
* Description:
treecompose decomposes the tree in continuation passing style.
Particularly, if tree is null, then the continuation is invoked.  If
tree is a non-nil atom, then function is called with teh atom and the
continuation.  If tree is a cons cell, then treecompose is called
recursively with the function, the car of the tree, and a new
continuation which will call treecompose with the function, the cdr of
the tree, and the original continuation.
* Examples:
;;; (defvar *tree-elements* '())
;;; => *TREE-ELEMENTS*
;;;
;;; (treecompose #'(lambda (atom K)
;;;                  (let ((*tree-elements* (list* atom *tree-elements*)))
;;;                    (funcall K)))
;;;              '(1 (2 . 3) ((4) 5) 6 . 7)
;;;              #'(lambda () 
;;;                  *tree-elements*))
;;; => (7 6 5 4 3 2 1)
* Notes:
The primary benefit of continuation passing decomposition of trees is
the dynamic scope in which the continuations are invoked."
  (cond
   ((null tree) (funcall K))
   ((atom tree) (funcall function tree K))
   ((treecompose 
     function (car tree)
     #'(lambda ()
         (treecompose function (cdr tree) K))))))

(defun spread-arglist (spreadable-arglist)
  "* Syntax:
spread-arglist spreadable-arglist-designator => list
* Description:
spread-arglist returns the designated argument list."
  (reduce 'list* spreadable-arglist :from-end t))

(defun parse-body (body &optional (documentationp t))
  "* Syntax:
parse-body body documentationp => forms, declarations, documentation
* Arguments and Values:
- body---a list
- documentationp---a generalized boolean, default is true
- forms---a list of forms
- declarations---a list of declare expressions
- documentation---a string, or nil
* Description:
parse-body extracts the documentation string, the declarations, and
the forms from a body.  If documentationp then the parsing does not
recognize documentation strings and the third returned value will
always be nil. "
  (let ((documentations '())
        (declarations '()))
    (flet ((declarationp ()
             (and (listp (first body))
                  (eq 'declare (car (first body)))))
           (documentationp ()
             (and documentationp 
                  (stringp (first body))
                  (endp documentations)
                  (not (endp (rest body))))))
      (loop 
       (cond
        ((documentationp)
         (push (pop body) documentations))
        ((declarationp)
         (push (pop body) declarations))
        ((return (values body 
                         declarations
                         (first documentations)))))))))

) ; eval-when

(defun invoke-interning (key hash-table thunk)
  "* Syntax:
invoke-interning key thunk => value
* Arguments and Values:
- key---an object
- thunk---a function of zero arguments
* Description:
invoke-interning checks hash-table contains an entry for the key.  If
it does, then the corresponding value is returned.  Otherwise, the
thunk is invoked to produce a value which is stored in the hash table
\(as the value for the key\) and is returend."
  (multiple-value-bind (object presentp)
      (gethash key hash-table)
    (if presentp object
      (setf (gethash key hash-table)
            (funcall thunk)))))

(defmacro interning ((keyform hash-table-form) &body body)
  "* Syntax:
interning (keyform hash-table-form) form* => value
* Arguments and Values:
- keyform---a form, evaluated to produce key
- hash-table-form---a form, evaluated to produce hash-table
- form---a form
* Description:
interning checks whether hash-table contains an entry for the key.  If
it does, then the value for the key is returned.  Otherwise the forms
are evaluated to produce a value which is stored as the value for the
key in the hash table, and this value is returned."
  `(invoke-interning ,keyform
                     ,hash-table-form 
                     #'(lambda () (progn ,@body))))

(defun strict-mapcar (function list &rest lists)
  (let ((length (list-length list)))
    (assert (every #'(lambda (list)
                       (= length (list-length list)))
                   lists)
        () 
      "All lists provided to strict-mapcar must be the same length.")
    (apply 'mapcar function list lists)))

(defmacro nlet (name bindings &body body)
  `(labels ((,name ,(mapcar 'first bindings)
              ,@body))
     (,name ,@(mapcar 'second bindings))))

(defun strcat (&rest string-designators)
  (with-output-to-string (*standard-output*)
    (dolist (stringd string-designators)
      (write-string (string stringd)))))
