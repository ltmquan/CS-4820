
#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 5.
 Due: 3/12 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 5".

 The group members are:

 Quan Luu (put the names of the group members here)
 
 To make sure that we are all on the same page, build the latest
 version of ACL2s, as per HWK1. You are going to be using SBCL, which
 you already have, due to the build process in

 Next, install quicklisp. See https://www.quicklisp.org/beta/. 

 To make sure everything is OK with quicklisp and to initialize it,
 start sbcl and issue the following commands

 (load "~/quicklisp/setup.lisp")
 (ql:quickload :trivia)
 (ql:quickload :cl-ppcre)
 (ql:quickload :let-plus)
 (setf ppcre:*allow-named-registers* t)
 (exit) 

 Next, clone the ACL2s interface repository:
 (https) https://gitlab.com/acl2s/external-tool-support/interface.git
 (ssh)   git@gitlab.com:acl2s/external-tool-support/interface.git

 This repository includes scripts for interfacing with ACL2s from lisp.
 Put this directory in the ...books/acl2s/ of your ACL2 repository, or 
 use a symbolic link.

 Now, certify the books, by going to ...books/acl2s/interface and
 typing 

 "cert.pl -j 4 top"

 Look at the documentation for cert.pl. If cert.pl isn't in your path,
 then use

 "...books/build/cert.pl -j 4 top"

 The "-j 4" option indicates that you want to run up to 4 instances of
 ACL2 in parallel. Set this number to the number of cores you have.

 As mentioned at the beginning of the semester, some of the code we
 will write is in Lisp. You can find the common lisp manual online in
 various formats by searching for "common lisp manual."

 Other references that you might find useful and are available online
 include
 
 - Common Lisp: A Gentle Introduction to Symbolic Computation by David
   Touretzky
 - ANSI Common Lisp by Paul Graham
 
|#

(in-package "ACL2S")

;; Now for some ACL2s systems programming.

;; This book is already included in ACL2s, so this is a no-op, but I'm
;; putting it here so that you can see where the code for ACL2s
;; systems programming is coming from.
(include-book "acl2s/interface/top" :dir :system)
(set-ignore-ok t)

;; This gets us to raw lisp.
:q

#| 

 The interface books provide us with the ability to call the theorem
 prover within lisp, which will be useful in checking your code. 

 Here are some examples you can try. acl2s-compute is the form you use
 when you are using ACL2s to compute something, e.g., running a
 function on some input. acl2s-query is the form you use when you are
 querying ACL2s, e.g., a property without a name. If the property has
 a name, then that is not a query, but an event and you have to use
 acl2s-event.

 (acl2s-compute '(+ 1 2))
 (acl2s-query '(property (p q :all)
                 (iff (=> p q)
                      (v (! p) q))))
|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. Links to online documentation
 for the software libraries are provided below.

|#

(load "~/quicklisp/setup.lisp")

; See https://lispcookbook.github.io/cl-cookbook/pattern_matching.html
(ql:quickload :trivia)

; See https://www.quicklisp.org/beta/UNOFFICIAL/docs/cl-ppcre/doc/index.html
(ql:quickload :cl-ppcre)

; See https://github.com/sharplispers/let-plus
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

;; We import acl2s-compute and acl2s-query into our package.

(import 'acl2s-interface-internal::(acl2s-compute acl2s-query))

#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t)
    (not     :arity 1 :identity -   :idem nil :sink -)
    (implies :arity 2 :identity -   :idem nil :sink -)
    (iff     :arity - :identity t   :idem nil :sink -)
    (xor     :arity - :identity nil :idem nil :sink -)
    (if      :arity 3 :identity -   :idem nil :sink -)))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun key-alist->val (k l)
  (let* ((in (assoc k l :test #'equal)))
    (values (cdr in) in)))

(key-alist->val 'iff *p-ops*)

(defun key-list->val (k l)
  (let* ((in (member k l :test #'equal)))
    (values (cadr in) in)))

(key-list->val ':arity  (key-alist->val 'iff *p-ops*))

(defun pfun-key->val (fun key)
  (key-list->val key (key-alist->val fun *p-ops*)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defparameter *booleans* '(t nil))

(defun booleanp (x)
  (in x *booleans*))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (key-list->val :arity (key-alist->val pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))

#|
 
 Here is the definition of a propositional formula. 
 
|#

(defun p-formulap (f)
  (match f
    ((type boolean) t) ; don't need this case, but here for emphasis
    ((type symbol) t)
    ((list* pop args)
     (if (p-funp pop)
         (pfun-argsp pop args)
       t))
    (_ nil)))

#|
 
 Notice that in addition to propositional variables, we allow atoms
 such as (foo x). 

 Here are some assertions (see the common lisp manual).
 
|#

(assert (p-formulap '(and)))
(assert (p-formulap '(and x y z)))
(assert (p-formulap '(and t nil)))
(assert (not (p-formulap '(implies x t nil))))
(assert (p-formulap 'q))
(assert (p-formulap '(implies (foo x) (bar y))))
(assert (p-formulap '(iff p q r s t)))
(assert (p-formulap '(xor p q r s t)))
(assert (not (p-formulap '(if p q r t))))

#|

 The propositional skeleton is what remains when we remove
 non-variable atoms.

|#

(defun p-skeleton-args (args amap acc)
  (if (endp args)
      (values (reverse acc) amap)
    (let+ (((&values na namap)
            (p-skeleton (car args) amap)))
          (p-skeleton-args (cdr args) namap (cons na acc)))))

(defun p-skeleton (f &optional amap) ;amap is nil if not specified
  (match f
    ((type symbol) (values f amap))
    ((list* pop args)
     (if (p-funp pop)
         (let+ (((&values nargs namap)
                 (p-skeleton-args args amap nil)))
               (values (cons pop nargs) namap))
       (let ((geta (key-alist->val f amap)))
         (if geta
             (values geta amap)
           (let ((gen (gentemp "P")))
             (values gen (acons f gen amap)))))))
    (_ (error "Not a p-formula"))))

#|

 Here are some examples you can try.

(p-skeleton
 '(or p q r s))

(p-skeleton
 '(iff q r))

(p-skeleton
 '(or p (iff q r)))

(p-skeleton
 '(or p (iff q r) (and p q p) (if p (and p q) (or p q))))

(p-skeleton
 '(iff p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(xor p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(iff p p q (foo t r) (foo s nil) (or p q)))

(p-skeleton
 '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))

|#

#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun nary-to-2ary (fun args)
  (let ((identity (pfun-key->val fun :identity)))
    (match args
      (nil identity)
      ((list x) (to-acl2s x))
      (_ (acl2s::xxxjoin (to-acl2s fun) (mapcar #'to-acl2s args))))))

(defun to-acl2s (f)
  (let ((s (p-skeleton f)))
    (match s
      ((type symbol) (intern (symbol-name f) "ACL2S"))
      ((cons x xs)
       (if (in x '(iff xor))
           (nary-to-2ary x xs)
         (mapcar #'to-acl2s f)))
      (_ f))))

(to-acl2s '(and a b c d))
(to-acl2s '(iff a b c d))
(to-acl2s '(xor a b c d))

(defun pvars- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (and (p-funp op)
          (reduce #'append (mapcar #'pvars- args))))))

(defun pvars (f) (remove-dups (pvars- f)))

(pvars '(and t (iff nil) (iff t nil t nil) p q))
(pvars '(iff p p q (foo t r) (foo s nil) (or p q)))
(pvars '(if p q (or r (foo t s) (and (not q)))))

(defun boolean-hyps (l)
  (reduce #'append
          (mapcar #'(lambda (x) `(,x :bool))
                  (mapcar #'to-acl2s l))))

(boolean-hyps '(p q r))

(defun acl2s-check-equal (f g)
  (let* ((iff `(iff ,f ,g))
         (siff (p-skeleton iff))
	 (pvars (pvars siff))
	 (aiff (to-acl2s siff))
         (af (second aiff))
         (ag (third aiff))
         (bhyps (boolean-hyps pvars)))
    (acl2s-query
     `(acl2s::property ,bhyps (acl2s::iff ,af ,ag)))))

;; And some simple examples.
(acl2s-check-equal 'p 'p)
(acl2s-check-equal 'p 'q)

; Here is how to check if the query succeeded
(assert (== (car (acl2s-check-equal 'p 'p)) nil))

; So, here's a useful function
(defun assert-acl2s-equal (f g)
  (assert (== (car (acl2s-check-equal f g)) nil)))

(assert-acl2s-equal 'p 'p)

#|

; This will lead to an error. Try it.
; In sbcl :top gets you out of the debugger.
(assert-acl2s-equal 'p 'q)

|#

; Here is how we can use ACL2s to check our code.
(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c))))))
  (assert-acl2s-equal x t))

(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))
       (sx (p-skeleton x)))
  (assert-acl2s-equal sx t))


#|
 
 Question 1. (25 pts)

 Define function, p-simplify that given a propositional formula
 returns an equivalent propositional formula with the following
 properties. 

 A. The skeleton of the returned formula is either a constant or does
 not include any constants. For example:

 (and p t (foo t nil) q) should be simplified to (and p (foo t nil) q)
 (and p t (foo t b) nil) should be simplified to nil

 B. Flatten expressions, e.g.:

 (and p q (and r s) (or u v)) is not flat, but this is
 (and p q r s (or u v))

 A formula of the form (op ...) where op is a Boolean operator of
 arbitrary arity (ie, and, or, iff) applied to 0 or 1 arguments is not
 flat. For example, replace (and) with t. 

 A formula of the form (op ... (op ...)) where op is a Boolean
 operator of arbitrary arity is not flat. For example, replace (and p
 q (and r s)) with (and p q r s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain
 
 (not (not f))
 (not (iff ...))
 (not (xor ...))

 E. Apply Shannon expansions in 61-67.

 For example

 (and (or p q) (or r q p) p) should be simplified to

 p because (and (or t q) (or r q t) p) is (and t t p) is p

 F. Simplify formulas so that no subexpressions of the form

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or x y (foo a b) z (not (foo a b)) w) should be simplified to 

 t 

 Make sure that your algorithm is as efficient as you can make
 it. The idea is to use this simplification as a preprocessing step,
 so it needs to be fast. 

 You are not required to perform any other simplifications beyond
 those specified above. If you do, your simplifier must be guaranteed
 to always return something that is simpler that what would be
 returned if you just implemented the simplifications explicitly
 requested. Also, if you implement any other simplifications, your
 algorithm must run in comparable time (eg, no validity checking).
 Notice some simple consequences. You cannot transform the formula to
 an equivalent formula that uses a small subset of the
 connectives (such as not/and). If you do that, the formula you get
 can be exponentially larger than the input formula, as we have
 discussed in class. Notice that even negation normal form (NNF) can
 increase the size of a formula. Such considerations are important
 when you use Tseitin, because experience has shown that even
 transformations such as NNF are usually a bad idea when generating
 CNF, as they tend to result in CNF formulas that take modern solvers
 longer to analyze.

 Test your definition with assert-acl2s-equal using at least 10
 propositional formulas that include non-variable atoms, all of the
 operators, deeply nested formulas, etc.

 
|#

;; Utility functions (defined before p-simplify)

(defun atomp (a)
  (or (symbolp a)
      (and (consp a) (not (p-funp (car a))))))

(defun negate (f)
  (match f
    ((list 'not x) x)
    (_ (list 'not f))))

(defun flatten-op (op args)
  (loop for a in args
        if (and (consp a) (eq (car a) op))
          append (cdr a)
        else collect a))

(defun subst-lit (lit val f)
  (cond
    ((equal f lit) val)
    ((equal f (negate lit)) (if val nil t))
    ((atomp f) f)
    ((consp f)
     (let* ((op (car f))
            (args (cdr f))
            (new-args (mapcar (lambda (a) (subst-lit lit val a)) args)))
       (if (every #'eq args new-args)
           f
         (cons op new-args))))
    (t f)))

(defun has-complement (args)
  (let ((s (make-hash-table :test #'equal)))
    (loop for a in args do (setf (gethash a s) t))
    (loop for a in args
          thereis (gethash (negate a) s))))

(defun dedup-ordered (args)
  (let ((seen (make-hash-table :test #'equal))
        (result nil))
    (dolist (a args (nreverse result))
      (unless (gethash a seen)
        (setf (gethash a seen) t)
        (push a result)))))

(defun remove-pairs (args)
  (let ((counts (make-hash-table :test #'equal))
        (order nil))
    (loop for a in args do
      (when (not (gethash a counts))
        (push a order))
      (incf (gethash a counts 0)))
    (let ((sorted (nreverse order)))
      (loop for a in sorted
            when (oddp (gethash a counts))
            collect a))))

(defun remove-complement-pairs (args)
  (let ((tbl (make-hash-table :test #'equal))
        (order nil)
        (neg-count 0))
    (dolist (a args)
      (unless (gethash a tbl)
        (push a order))
      (incf (gethash a tbl 0)))
    (let ((ord (nreverse order)))
      (dolist (a ord)
        (let* ((comp (negate a))
               (a-count (gethash a tbl 0))
               (c-count (gethash comp tbl 0)))
          (when (and (> a-count 0) (> c-count 0))
            (let ((cancel (min a-count c-count)))
              (incf neg-count cancel)
              (decf (gethash a tbl) cancel)
              (decf (gethash comp tbl) cancel)))))
      (let ((result nil))
        (dolist (a ord)
          (dotimes (_ (gethash a tbl 0))
            (push a result)))
        (values (nreverse result) neg-count)))))

(defun p-simplify (f)
  (labels
    ((litp (a)
       (or (atomp a)
           (and (consp a) (eq (car a) 'not) (atomp (cadr a)))))

     (shannon (args val)
       (let* ((lit-set (make-hash-table :test #'equal))
              (lits nil)
              (changed nil))
         (dolist (a args)
           (when (litp a)
             (setf (gethash a lit-set) t)
             (push a lits)))
         (when (null lits)
           (return-from shannon (values args nil)))
         (let ((new-args
                (mapcar (lambda (x)
                          (if (gethash x lit-set) x
                            (let* ((substed
                                    (reduce (lambda (f lit)
                                              (subst-lit lit val f))
                                            lits :initial-value x))
                                   (simplified (p-simplify substed)))
                              (when (not (equal simplified x))
                                (setf changed t))
                              simplified)))
                        args)))
           (values new-args changed))))

     (simp-not (arg)
       (match arg
         ((eql t) nil)
         ((eql nil) t)
         ((list 'not a) a)
         ((list* 'iff args)
          `(iff ,(simp-not (car args)) ,@(cdr args)))
         ((list* 'xor args)
          `(xor ,(simp-not (car args)) ,@(cdr args)))
         (_ (list 'not arg))))

     (simp-and (args)
       (let* ((flat (flatten-op 'and args)))
         (when (member nil flat :test #'equal)
           (return-from simp-and nil))
         (let* ((no-id (remove t flat :test #'equal))
                (dedup (dedup-ordered no-id)))
           (when (has-complement dedup)
             (return-from simp-and nil))
           (multiple-value-bind (result changed) (shannon dedup t)
             (if changed
                 (p-simplify (cons 'and result))
               (match result
                 (nil t)
                 ((list x) x)
                 (_ (cons 'and result))))))))

     (simp-or (args)
       (let* ((flat (flatten-op 'or args)))
         (when (member t flat :test #'equal)
           (return-from simp-or t))
         (let* ((no-id (remove nil flat :test #'equal))
                (dedup (dedup-ordered no-id)))
           (when (has-complement dedup)
             (return-from simp-or t))
           (multiple-value-bind (result changed) (shannon dedup nil)
             (if changed
                 (p-simplify (cons 'or result))
               (match result
                 (nil nil)
                 ((list x) x)
                 (_ (cons 'or result))))))))

     (simp-implies (a b)
       (cond
         ((equal a t) b)
         ((equal a nil) t)
         ((equal b t) t)
         ((equal b nil) (simp-not a))
         ((equal a b) t)
         (t (list 'implies a b))))

     (simp-iff (args)
       (let* ((flat (flatten-op 'iff args))
              (no-id (remove t flat :test #'equal))
              (no-pairs (remove-pairs no-id)))
         (let* ((nils (count nil no-pairs :test #'equal))
                (no-nil (remove nil no-pairs :test #'equal)))
           (multiple-value-bind (cleaned neg-count)
               (remove-complement-pairs no-nil)
             (let* ((total-neg (+ nils neg-count))
                    (result (if (oddp total-neg)
                                (if cleaned
                                    (cons (simp-not (car cleaned))
                                          (cdr cleaned))
                                  (list nil))
                              cleaned)))
               (match result
                 (nil t)
                 ((list x) x)
                 (_ (cons 'iff result))))))))

     (simp-xor (args)
       (let* ((flat (flatten-op 'xor args))
              (no-id (remove nil flat :test #'equal))
              (no-pairs (remove-pairs no-id)))
         (let* ((ts (count t no-pairs :test #'equal))
                (no-t (remove t no-pairs :test #'equal)))
           (multiple-value-bind (cleaned neg-count)
               (remove-complement-pairs no-t)
             (let* ((total-neg (+ ts neg-count))
                    (result (if (oddp total-neg)
                                (if cleaned
                                    (cons (simp-not (car cleaned))
                                          (cdr cleaned))
                                  (list t))
                              cleaned)))
               (match result
                 (nil nil)
                 ((list x) x)
                 (_ (cons 'xor result))))))))

     (simp-if (a b c)
       (cond
         ((equal a t) b)
         ((equal a nil) c)
         ((equal b c) b)
         ((and (equal b t) (equal c nil)) a)
         ((and (equal b nil) (equal c t)) (simp-not a))
         (t (list 'if a b c)))))

    (match f
      ((type symbol) f)
      ((list* pop args)
       (let ((simp-args (mapcar #'p-simplify args)))
         (match pop
           ('not     (simp-not (car simp-args)))
           ('and     (simp-and simp-args))
           ('or      (simp-or simp-args))
           ('implies (simp-implies (car simp-args) (cadr simp-args)))
           ('iff     (simp-iff simp-args))
           ('xor     (simp-xor simp-args))
           ('if      (simp-if (car simp-args) (cadr simp-args) (caddr simp-args)))
           (_        (cons pop simp-args)))))
      (_ f))))

(assert-acl2s-equal
 (p-simplify '(and p t (foo t nil) q))
 '(and p (foo t nil) q))

(assert-acl2s-equal
 (p-simplify '(and p t (foo t b) nil))
 'nil)

(assert-acl2s-equal
 (p-simplify '(and p q (and r s) (or u v)))
 '(and p q r s (or u v)))

(assert-acl2s-equal
 (p-simplify '(and))
 't)

(assert-acl2s-equal
 (p-simplify '(not (not (foo a b))))
 '(foo a b))

(assert-acl2s-equal
 (p-simplify '(not (iff p q)))
 '(iff (not p) q))

(assert-acl2s-equal
 (p-simplify '(and (or p q) (or r q p) p))
 'p)

(assert-acl2s-equal
 (p-simplify '(or x y (foo a b) z (not (foo a b)) w))
 't)

(assert-acl2s-equal
 (p-simplify '(implies t (if nil p q)))
 'q)

(assert-acl2s-equal
 (p-simplify '(xor p p q))
 'q)

(assert-acl2s-equal
 (p-simplify '(iff p p q))
 'q)

(assert-acl2s-equal
 (p-simplify '(or nil (or nil p q) nil))
 '(or p q))

(assert-acl2s-equal
 (p-simplify '(and (or (not (not (bar x y))) z)
                   (implies t (foo a b))
                   (iff r r)))
 '(and (or (bar x y) z) (foo a b)))

(assert-acl2s-equal
 (p-simplify '(if (foo x) (and p q) (and p q)))
 '(and p q))

(assert-acl2s-equal
 (p-simplify '(and (foo a) (or (foo a) (bar b)) (not (not (baz c)))))
 '(and (foo a) (baz c)))

#|

 Question 2. (20 pts)

 Define tseitin, a function that given a propositional formula,
 something that satisfies p-formulap, applies the tseitin
 transformation to generate a CNF formula that is equi-satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 You should simplify the formula first, using p-simplify, but do not
 perform any other simplifications. Any simpification you want to
 perform must be done in p-simplify.

 Test tseitin using with assert-acl2s-equal using at least 10
 propositional formulas.

|#

(defparameter *tseitin-counter* 0)

(defun tseitin-fresh ()
  (intern (format nil "T~A" (incf *tseitin-counter*))))

(defun tseitin (f)
  (setf *tseitin-counter* 0)
  (let* ((simplified (p-simplify f)))
    (cond
      ((equal simplified t) t)
      ((equal simplified nil) nil)
      (t
       (let ((clauses nil))
         (labels
           ((fresh () (tseitin-fresh))

            (bin (op args)
              (if (cddr args)
                  (list op (car args) (bin op (cdr args)))
                (cons op args)))

            (process (f)
              (cond
                ((atomp f) f)
                (t
                 (let* ((op (car f))
                        (args (cdr f)))
                   (when (and (member op '(iff xor)) (cddr args))
                     (let ((b (bin op args)))
                       (setf op (car b))
                       (setf args (cdr b))))
                   (let* ((cvs (mapcar #'process args))
                          (v (fresh)))
                     (ecase op
                       (not
                        (let ((a (first cvs)))
                          (push (list (negate v) (negate a)) clauses)
                          (push (list v a) clauses)))
                       (and
                        (dolist (a cvs)
                          (push (list (negate v) a) clauses))
                        (push (cons v (mapcar #'negate cvs)) clauses))
                       (or
                        (dolist (a cvs)
                          (push (list (negate a) v) clauses))
                        (push (cons (negate v) cvs) clauses))
                       (implies
                        (let ((a (first cvs)) (b (second cvs)))
                          (push (list (negate v) (negate a) b) clauses)
                          (push (list v a) clauses)
                          (push (list v (negate b)) clauses)))
                       (iff
                        (let ((a (first cvs)) (b (second cvs)))
                          (push (list (negate v) (negate a) b) clauses)
                          (push (list (negate v) a (negate b)) clauses)
                          (push (list (negate a) (negate b) v) clauses)
                          (push (list a b v) clauses)))
                       (xor
                        (let ((a (first cvs)) (b (second cvs)))
                          (push (list (negate v) (negate a) (negate b)) clauses)
                          (push (list (negate v) a b) clauses)
                          (push (list (negate a) b v) clauses)
                          (push (list a (negate b) v) clauses)))
                       (if
                        (let ((a (first cvs)) (b (second cvs)) (c (third cvs)))
                          (push (list (negate v) (negate a) b) clauses)
                          (push (list (negate v) a c) clauses)
                          (push (list (negate a) (negate b) v) clauses)
                          (push (list a (negate c) v) clauses))))
                     v))))))

           (let ((top (process simplified)))
             (push (list top) clauses)
             (cons 'and
                   (mapcar (lambda (c)
                             (if (cdr c)
                                 (cons 'or c)
                               (car c)))
                           (nreverse clauses))))))))))

(assert-acl2s-equal (tseitin t) t)
 
(assert-acl2s-equal (tseitin nil) nil)
 
(assert-acl2s-equal
 (tseitin '(not p))
 '(AND (OR (NOT T1) (NOT P)) (OR T1 P) T1))
 
(assert-acl2s-equal
 (tseitin '(and p q))
 '(AND (OR (NOT T1) P) (OR (NOT T1) Q) (OR T1 (NOT P) (NOT Q)) T1))
 
(assert-acl2s-equal
 (tseitin '(or p q))
 '(AND (OR (NOT P) T1) (OR (NOT Q) T1) (OR (NOT T1) P Q) T1))
 
(assert-acl2s-equal
 (tseitin '(implies p q))
 '(AND (OR (NOT T1) (NOT P) Q) (OR T1 P) (OR T1 (NOT Q)) T1))
 
(assert-acl2s-equal
 (tseitin '(iff p q))
 '(AND (OR (NOT T1) (NOT P) Q) (OR (NOT T1) P (NOT Q))
       (OR (NOT P) (NOT Q) T1) (OR P Q T1) T1))
 
(assert-acl2s-equal
 (tseitin '(xor p q))
 '(AND (OR (NOT T1) (NOT P) (NOT Q)) (OR (NOT T1) P Q)
       (OR (NOT P) Q T1) (OR P (NOT Q) T1) T1))
 
(assert-acl2s-equal
 (tseitin '(if p q r))
 '(AND (OR (NOT T1) (NOT P) Q) (OR (NOT T1) P R)
       (OR (NOT P) (NOT Q) T1) (OR P (NOT R) T1) T1))
 
(assert-acl2s-equal
 (tseitin '(or (and p q) r))
 '(AND (OR (NOT T1) P) (OR (NOT T1) Q) (OR T1 (NOT P) (NOT Q))
       (OR (NOT T1) T2) (OR (NOT R) T2) (OR (NOT T2) T1 R) T2))
 
(assert-acl2s-equal
 (tseitin '(not (iff (foo a) q)))
 '(AND (OR (NOT T1) (NOT (FOO A))) (OR T1 (FOO A))
       (OR (NOT T2) (NOT T1) Q) (OR (NOT T2) T1 (NOT Q))
       (OR (NOT T1) (NOT Q) T2) (OR T1 Q T2) T2))
 
(assert-acl2s-equal
 (tseitin '(and (or a b) (implies (foo x y) (not c))))
 '(AND (OR (NOT A) T1) (OR (NOT B) T1) (OR (NOT T1) A B)
       (OR (NOT T2) (NOT C)) (OR T2 C)
       (OR (NOT T3) (NOT (FOO X Y)) T2) (OR T3 (FOO X Y))
       (OR T3 (NOT T2))
       (OR (NOT T4) T1) (OR (NOT T4) T3)
       (OR T4 (NOT T1) (NOT T3)) T4))

#|

 Question 3. (30 pts)

 Define DP, a function that given a propositional formula in CNF,
 applies the Davis-Putnam algorithm to determine if the formula is
 satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DP returns 'sat and a satisfying assignment: an
 alist mapping each atom in the formula to t/nil. Use values to return
 multiple values.

 If it is usat, return 'unsat.

 Do some profiling

 Test DP using with assert-acl2s-equal using at least 10
 propositional formulas. 

 It is easy to extend dp to support arbitrary formulas by using
 tseitin to generate CNF.

|#

(defun lit-var (lit)
  (if (and (consp lit) (eq (car lit) 'not))
      (cadr lit)
    lit))
 
(defun negatedp (lit)
  (and (consp lit) (eq (car lit) 'not)))
 
(defun parse-cnf (f)
  (cond
    ((equal f t) nil)
    ((equal f nil) '(()))
    ((and (consp f) (eq (car f) 'and))
     (mapcar #'parse-clause (cdr f)))
    (t (list (parse-clause f)))))
 
(defun parse-clause (c)
  (cond
    ((and (consp c) (eq (car c) 'or))
     (cdr c))
    (t (list c))))
 
(defun propagate (lit clauses)
  (let ((neg (negate lit))
        (result nil))
    (dolist (c clauses (nreverse result))
      (unless (member lit c :test #'equal)
        (push (remove neg c :test #'equal) result)))))
 
(defun find-pure (clauses)
  (let ((pos (make-hash-table :test #'equal))
        (neg (make-hash-table :test #'equal)))
    (dolist (c clauses)
      (dolist (lit c)
        (if (negatedp lit)
            (setf (gethash (lit-var lit) neg) t)
          (setf (gethash lit pos) t))))
    (maphash (lambda (v _)
               (declare (ignore _))
               (unless (gethash v neg)
                 (return-from find-pure v)))
             pos)
    (maphash (lambda (v _)
               (declare (ignore _))
               (unless (gethash v pos)
                 (return-from find-pure (list 'not v))))
             neg)
    nil))
 
(defun choose-var (clauses)
  (let ((pos-count (make-hash-table :test #'equal))
        (neg-count (make-hash-table :test #'equal))
        (vars nil))
    (dolist (c clauses)
      (dolist (lit c)
        (let ((v (lit-var lit)))
          (unless (gethash v pos-count)
            (setf (gethash v pos-count) 0)
            (setf (gethash v neg-count) 0)
            (push v vars))
          (if (negatedp lit)
              (incf (gethash v neg-count))
            (incf (gethash v pos-count))))))
    (let ((best-var nil)
          (best-score most-positive-fixnum))
      (dolist (v vars best-var)
        (let ((score (* (gethash v pos-count) (gethash v neg-count))))
          (when (< score best-score)
            (setf best-score score)
            (setf best-var v)))))))
 
(defun tautologyp (clause)
  (let ((s (make-hash-table :test #'equal)))
    (dolist (lit clause)
      (setf (gethash lit s) t))
    (dolist (lit clause nil)
      (when (gethash (negate lit) s)
        (return t)))))
 
(defun resolve-pairs (var pos neg)
  (let ((neg-var (negate var))
        (seen (make-hash-table :test #'equal))
        (result nil))
    (dolist (pc pos)
      (dolist (nc neg)
        (let* ((pc-rest (remove var pc :test #'equal))
               (nc-rest (remove neg-var nc :test #'equal))
               (resolvent (dedup-ordered (append pc-rest nc-rest))))
          (unless (or (tautologyp resolvent)
                      (gethash resolvent seen))
            (setf (gethash resolvent seen) t)
            (push resolvent result)))))
    (nreverse result)))
 
(defun clause-satisfied-p (clause assignment)
  (dolist (lit clause nil)
    (let* ((v (lit-var lit))
           (pair (assoc v assignment :test #'equal)))
      (when pair
        (let ((val (cdr pair)))
          (when (if (negatedp lit) (not val) val)
            (return t)))))))
 
(defun reconstruct (assignment resolution-stack)
  (let ((final assignment))
    (dolist (entry resolution-stack final)
      (let ((var (first entry))
            (neg-clauses (third entry)))
        (let ((test (acons var t final)))
          (if (every (lambda (c) (clause-satisfied-p c test)) neg-clauses)
              (setf final test)
            (setf final (acons var nil final))))))))
 
(defun dp (f)
  (let ((clauses (parse-cnf f))
        (assignment nil)
        (resolution-stack nil))
    (loop
      (when (some #'null clauses)
        (return-from dp 'unsat))
      (when (null clauses)
        (return-from dp
          (values 'sat (reconstruct assignment resolution-stack))))
      (let ((unit (find-if (lambda (c) (= (length c) 1)) clauses)))
        (if unit
            (let ((lit (car unit)))
              (setf clauses (propagate lit clauses))
              (push (cons (lit-var lit) (if (negatedp lit) nil t)) assignment))
          (let ((pure (find-pure clauses)))
            (if pure
                (progn
                  (setf clauses (propagate pure clauses))
                  (push (cons (lit-var pure) (if (negatedp pure) nil t)) assignment))
              (let* ((var (choose-var clauses))
                     (neg-lit (negate var))
                     (pos nil) (neg nil) (rest nil))
                (dolist (c clauses)
                  (cond
                    ((member var c :test #'equal) (push c pos))
                    ((member neg-lit c :test #'equal) (push c neg))
                    (t (push c rest))))
                (let ((resolvents (resolve-pairs var pos neg)))
                  (setf clauses (append rest resolvents))
                  (push (list var pos neg) resolution-stack))))))))))

(time (assert-acl2s-equal (dp '(and p)) 'sat))

(assert-acl2s-equal (dp '(and p (not p))) 'unsat)

(assert-acl2s-equal (dp '(and (or p q) (or (not p) q))) 'sat)

(assert-acl2s-equal (dp '(and (or p) (or (not p)))) 'unsat)

(assert-acl2s-equal (dp '(and (or p q) (or p (not q)) (or (not p) q) (or (not p) (not q)))) 'unsat)

(assert-acl2s-equal (dp '(and (or (foo a) (bar b)) (or (not (foo a)) (bar b)))) 'sat)

(assert-acl2s-equal (dp '(and (or p q r) (or (not p) q) (or (not q) r) (or p (not r)))) 'sat)

(assert-acl2s-equal (dp '(and (or (foo x) (bar y))
                              (or (foo x) (not (bar y)))
                              (or (not (foo x)) (bar y))
                              (or (not (foo x)) (not (bar y)))))
		    'unsat)

(assert-acl2s-equal (dp (tseitin '(or (and p q) r))) 'sat)

(assert-acl2s-equal (dp (tseitin '(or p (not p)))) 'sat)

(assert-acl2s-equal (dp (tseitin '(and p (not p)))) 'unsat)

(assert-acl2s-equal (dp (tseitin '(and (implies p q) (implies q r) p))) 'sat)

#|

 Question 4.

 Part1: (25pts) Profile DP and make it as efficient as possible. If it
 meets the efficiency criteria of the evaluator, you get credit. The
 fastest submission will get 20 extra points, no matter how slow. To
 generate interesting problems, see your book.

 Part 2: (30pts) Define DPLL, a function that given a propositional
 formula in CNF, applies the DPLL algorithm to determine if the
 formula is satisfiable. You have to implement the iterative with
 backjumping version of DPLL from the book.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DPLL returns 'sat and a satisfying assignment:
 an alist mapping each atom in the formula to t/nil. Use values to
 return multiple values.

 If it is usat, return 'unsat.

 Test DPLL using with assert-acl2s-equal using at least 10
 propositional formulas.

 The fastest submission will get 20 extra points, no matter how
 slow. To generate interesting problems, see your book.

|#

(defun collect-vars (clauses)
  (let ((seen (make-hash-table :test #'equal))
        (result nil))
    (dolist (c clauses)
      (dolist (lit c)
        (let ((v (lit-var lit)))
          (unless (gethash v seen)
            (setf (gethash v seen) t)
            (push v result)))))
    (nreverse result)))
 
(defun dpll (f)
  (cond
    ((equal f t) (values 'sat nil))
    ((equal f nil) 'unsat)
    (t (dpll-solve (parse-cnf f)))))
 
(defun dpll-solve (initial-clauses)
  (when (member nil initial-clauses :test #'equal)
    (return-from dpll-solve 'unsat))
  (let* ((n (length initial-clauses))
         (clause-db (make-array n :fill-pointer n :adjustable t
                                :initial-contents initial-clauses))
         (cw1 (make-array n :fill-pointer n :adjustable t :initial-element nil))
         (cw2 (make-array n :fill-pointer n :adjustable t :initial-element nil))
         (watches (make-hash-table :test #'equal))
         (assign (make-hash-table :test #'equal))
         (levels (make-hash-table :test #'equal))
         (reasons (make-hash-table :test #'equal))
         (trail (make-array 200 :fill-pointer 0 :adjustable t))
         (qhead 0)
         (dl 0)
         (act (make-hash-table :test #'equal))
         (act-inc 1.0d0)
         (all-vars (collect-vars initial-clauses))
         (saved-phase (make-hash-table :test #'equal))
         (n-conflicts 0)
         (restart-limit 100)
         (seen (make-hash-table :test #'equal)))
 
    (dolist (v all-vars)
      (setf (gethash v act) 0.0d0)
      (setf (gethash v saved-phase) nil))
 
    (dotimes (i n)
      (dolist (lit (aref clause-db i))
        (incf (gethash (lit-var lit) act) 1.0d0)))
 
    (labels
      ((val-of (lit)
         (multiple-value-bind (v p) (gethash (lit-var lit) assign)
           (if (not p) :undef
             (if (negatedp lit) (not v) v))))
 
       (assigned-p (var)
         (nth-value 1 (gethash var assign)))
 
       (try-assign-lit (lit lvl reason-ci)
         (let* ((var (lit-var lit))
                (val (not (negatedp lit))))
           (multiple-value-bind (old-val present) (gethash var assign)
             (cond
               ((not present)
                (setf (gethash var assign) val
                      (gethash var levels) lvl
                      (gethash var reasons) reason-ci)
                (vector-push-extend var trail)
                t)
               ((eq old-val val) t)
               (t nil)))))
 
       (assign-lit (lit lvl reason-ci)
         (let ((var (lit-var lit))
               (val (not (negatedp lit))))
           (setf (gethash var assign) val
                 (gethash var levels) lvl
                 (gethash var reasons) reason-ci)
           (vector-push-extend var trail)))
 
       (undo-one ()
         (let ((var (vector-pop trail)))
           (setf (gethash var saved-phase) (gethash var assign))
           (remhash var assign)
           (remhash var levels)
           (remhash var reasons)))
 
       (backtrack-to (lvl)
         (loop while (and (> (fill-pointer trail) 0)
                          (> (gethash (aref trail (1- (fill-pointer trail))) levels) lvl))
               do (undo-one))
         (setf qhead (fill-pointer trail))
         (setf dl lvl))
 
       (add-watch (lit ci)
         (push ci (gethash lit watches)))
 
       (propagate ()
         (loop while (< qhead (fill-pointer trail)) do
           (let* ((var (aref trail qhead))
                  (val (gethash var assign))
                  (false-lit (if val (negate var) var))
                  (watchers (gethash false-lit watches))
                  (kept nil))
             (incf qhead)
             (setf (gethash false-lit watches) nil)
             (loop while watchers do
               (let ((ci (pop watchers)))
                 (let* ((w1-lit (aref cw1 ci))
                        (w2-lit (aref cw2 ci))
                        (other (if (equal w1-lit false-lit) w2-lit w1-lit)))
                   (cond
                     ((eq (val-of other) t)
                      (push ci kept))
                     (t
                      (let ((found nil))
                        (dolist (l (aref clause-db ci))
                          (when (and (not (equal l false-lit))
                                     (not (equal l other))
                                     (not (eq (val-of l) nil)))
                            (setf found l)
                            (return)))
                        (cond
                          (found
                           (if (equal (aref cw1 ci) false-lit)
                               (setf (aref cw1 ci) found)
                             (setf (aref cw2 ci) found))
                           (add-watch found ci))
                          (t
                           (push ci kept)
                           (cond
                             ((eq (val-of other) :undef)
                              (assign-lit other dl ci))
                             (t
                              (setf (gethash false-lit watches)
                                    (nconc (nreverse kept) watchers))
                              (return-from propagate ci)))))))))))
             (setf (gethash false-lit watches) (nreverse kept))))
         nil)
 
       (analyze (conflict-ci)
         (clrhash seen)
         (let ((learned nil)
               (counter 0)
               (idx (1- (fill-pointer trail)))
               (asserting-lit nil))
           (dolist (lit (aref clause-db conflict-ci))
             (let ((v (lit-var lit)))
               (setf (gethash v seen) t)
               (if (= (gethash v levels) dl)
                   (incf counter)
                 (push lit learned))))
           (loop
             (loop while (and (>= idx 0)
                              (not (gethash (aref trail idx) seen)))
                   do (decf idx))
             (when (< idx 0) (return))
             (let ((var (aref trail idx)))
               (decf idx)
               (decf counter)
               (when (<= counter 0)
                 (let ((val (gethash var assign)))
                   (setf asserting-lit (if val (negate var) var)))
                 (push asserting-lit learned)
                 (return))
               (let ((reason-ci (gethash var reasons)))
                 (when reason-ci
                   (dolist (lit (aref clause-db reason-ci))
                     (let ((v (lit-var lit)))
                       (when (and (not (equal v var))
                                  (not (gethash v seen)))
                         (setf (gethash v seen) t)
                         (if (= (gethash v levels) dl)
                             (incf counter)
                           (push lit learned)))))))))
           (dolist (lit learned)
             (incf (gethash (lit-var lit) act) act-inc))
           (setf act-inc (* act-inc (/ 1.0d0 0.95d0)))
           (let ((backjump-lvl 0))
             (dolist (lit learned)
               (let ((lvl (gethash (lit-var lit) levels 0)))
                 (when (and (< lvl dl) (> lvl backjump-lvl))
                   (setf backjump-lvl lvl))))
             (values learned backjump-lvl asserting-lit))))
 
       (add-learned-clause (learned asserting-lit)
         (let ((ci (fill-pointer clause-db)))
           (vector-push-extend learned clause-db)
           (vector-push-extend nil cw1)
           (vector-push-extend nil cw2)
           (cond
             ((= (length learned) 1)
              (setf (aref cw1 ci) (car learned)
                    (aref cw2 ci) nil))
             (t
              (let ((second-lit (find-if (lambda (l)
                                           (not (equal l asserting-lit)))
                                         learned)))
                (setf (aref cw1 ci) asserting-lit
                      (aref cw2 ci) second-lit)
                (add-watch asserting-lit ci)
                (add-watch second-lit ci))))
           ci))
 
       (pick-var ()
         (let ((best nil) (best-act -1.0d0))
           (dolist (v all-vars)
             (unless (assigned-p v)
               (let ((a (gethash v act 0.0d0)))
                 (when (> a best-act)
                   (setf best v best-act a)))))
           best)))
 
      ;; Initialize watches for clauses with 2+ literals
      ;; Collect unit clause literals for initial propagation
      (let ((init-conflict nil))
        (dotimes (i n)
          (let ((clause (aref clause-db i)))
            (cond
              ((= (length clause) 1)
               (setf (aref cw1 i) (car clause) (aref cw2 i) nil)
               (unless init-conflict
                 (unless (try-assign-lit (car clause) 0 nil)
                   (setf init-conflict t))))
              (t
               (let ((l1 (first clause))
                     (l2 (second clause)))
                 (setf (aref cw1 i) l1 (aref cw2 i) l2)
                 (add-watch l1 i)
                 (add-watch l2 i))))))
        (when init-conflict
          (return-from dpll-solve 'unsat)))
 
      ;; Initial BCP
      (let ((conflict (propagate)))
        (when conflict
          (return-from dpll-solve 'unsat)))
 
      ;; Main CDCL loop
      (loop
        ;; Restart check
        (when (>= n-conflicts restart-limit)
          (backtrack-to 0)
          (setf restart-limit (ceiling (* restart-limit 1.5))))
 
        (let ((var (pick-var)))
          (unless var
            (let ((result nil))
              (maphash (lambda (k v) (push (cons k v) result)) assign)
              (return-from dpll-solve (values 'sat result))))
          (incf dl)
          (let ((val (gethash var saved-phase)))
            (assign-lit (if val var (negate var)) dl nil))
          (let ((conflict (propagate)))
            (loop while conflict do
              (if (= dl 0)
                  (return-from dpll-solve 'unsat)
                (progn
                  (incf n-conflicts)
                  (multiple-value-bind (learned backjump-lvl asserting-lit)
                      (analyze conflict)
                    (let ((ci (add-learned-clause learned asserting-lit)))
                      (backtrack-to backjump-lvl)
                      (assign-lit asserting-lit backjump-lvl ci)
                      (setf conflict (propagate)))))))))))))
 
(assert-acl2s-equal (dpll '(and p)) 'sat)
 
(assert-acl2s-equal (dpll '(and p (not p))) 'unsat)
 
(assert-acl2s-equal (dpll '(and (or p q) (or (not p) q))) 'sat)
 
(assert-acl2s-equal (dpll '(and (or p) (or (not p)))) 'unsat)
 
(assert-acl2s-equal (dpll '(and (or p q) (or p (not q)) (or (not p) q) (or (not p) (not q)))) 'unsat)
 
(assert-acl2s-equal (dpll '(and (or (foo a) (bar b)) (or (not (foo a)) (bar b)))) 'sat)
 
(assert-acl2s-equal (dpll '(and (or p q r) (or (not p) q) (or (not q) r) (or p (not r)))) 'sat)
 
(assert-acl2s-equal (dpll '(and (or (foo x) (bar y))
                               (or (foo x) (not (bar y)))
                               (or (not (foo x)) (bar y))
                               (or (not (foo x)) (not (bar y))))) 'unsat)
 
(assert-acl2s-equal (dpll (tseitin '(or (and p q) r))) 'sat)
 
(assert-acl2s-equal (dpll (tseitin '(or p (not p)))) 'sat)
 
(assert-acl2s-equal (dpll (tseitin '(and p (not p)))) 'unsat)

(assert-acl2s-equal (dpll (tseitin '(and (implies p q) (implies q r) p))) 'sat)
