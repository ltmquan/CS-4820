#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Spring 2026

 Homework 7.
 Due: 4/18 (Midnight)

 For this assignment, work in groups of 1-3. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 7".

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

 Here are some examples you can try. 

 acl2s-compute is the form you use when you are using ACL2s to compute
 something, e.g., running a function on some input. 

 (acl2s-compute '(+ 1 2))

 acl2s-query is the form you use when you are querying ACL2s, e.g., a
 property without a name. If the property has a name, then that is not
 a query, but an event and you have to use acl2s-event.

 (acl2s-query 'acl2s::(property (p q :all)
                        (iff (=> p q)
                             (v (! p) q))))

 acl2s-arity is a function that determines if f is a function defined
 in ACL2s and if so, its arity (number of arguments). If f is not a
 function, then the arity is nil. Otherwise, the arity is a natural
 number. Note that f can't be a macro.

 (acl2s-arity 'acl2s::app)     ; is nil since app is a macro
 (acl2s-arity 'acl2s::bin-app) ; is 2

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

(import 'acl2s::(acl2s-compute acl2s-query))
(import 'acl2s-interface-extras::(acl2s-arity))


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
    (or      :arity - :identity nil :idem t   :sink t  )
    (not     :arity 1 :identity -   :idem nil :sink -  )
    (implies :arity 2 :identity -   :idem nil :sink -  )
    (iff     :arity - :identity t   :idem nil :sink -  )
    (if      :arity 3 :identity -   :idem nil :sink -  )))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))
(defparameter *fo-quantifiers* '(forall exists))
(defparameter *booleans* '(t nil))
(defparameter *fo-keywords*
  (append *p-funs* *booleans* *fo-quantifiers*))

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

(defun get-alist (k l)
  (cdr (assoc k l :test #'equal)))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defun booleanp (x)
  (in x *booleans*))

(defun no-dupsp (l)
  (or (endp l)
      (and (not (in (car l) (cdr l)))
           (no-dupsp (cdr l)))))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (get-key :arity (get-alist pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))


#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun to-acl2s (f)
  (match f
    ((type symbol) (intern (symbol-name f) "ACL2S"))
    ((list 'iff) t)
    ((list 'iff p) (to-acl2s p))
    ((list* 'iff args)
     (acl2s::xxxjoin 'acl2s::iff
                     (mapcar #'to-acl2s args)))
    ((cons x xs)
     (mapcar #'to-acl2s f))
    (_ f)))

#|

 A FO term is either a 

 constant symbol: a symbol whose name starts with "C" and is
 optionally followed by a natural number with no leading 0's, e.g., c0,
 c1, c101, c, etc are constant symbols, but c00, c0101, c01, etc are
 not. Notice that (gentemp "C") will create a new constant. Notice
 that symbol names  are case insensitive, so C1 is the same as c1.

 quoted constant: anything of the form (quote object) for any object

 constant object: a rational, boolean, string, character or keyword

 variable: a symbol whose name starts with "X", "Y", "Z", "W", "U" or
 "V" and is optionally followed by a natural number with no leading
 0's (see constant symbol). Notice that (gentemp "X") etc will create
 a new variable.

 function application: (f t1 ... tn), where f is a
 non-constant/non-variable/non-boolean/non-keyword symbol. The arity
 of f is n and every occurrence of (f ...)  in a term or formula has
 to have arity n. Also, if f is a defined function in ACL2s, its arity
 has to match what ACL2s expects. We allow functions of 0-arity.
 
|#

(defun char-nat-symbolp (s chars)
  (and (symbolp s)
       (let ((name (symbol-name s)))
         (and (<= 1 (len name))
              (in (char name 0) chars)
              (or (== 1 (len name))
                  (let ((i (parse-integer name :start 1 :junk-allowed t)))
                    (and (integerp i)
                         (<= 0 i)
                         (string= (format nil "~a~a" (char name 0) i)
                                  name))))))))

(defun constant-symbolp (s)
  (char-nat-symbolp s '(#\C)))

(defun variable-symbolp (s)
  (char-nat-symbolp s '(#\X #\Y #\Z #\W #\U #\V)))

(defun quotep (c)
  (and (consp c)
       (== (car c) 'quote)))

(defun constant-objectp (c)
  (typep c '(or boolean rational simple-string standard-char keyword)))

#|

Examples

(constant-objectp #\a)
(constant-objectp 0)
(constant-objectp 1/221)
(constant-objectp "hi there")
(constant-objectp t)
(constant-objectp nil)
(constant-objectp :hi)
(constant-objectp 'a)

(quotep '1)  ; recall that '1 is evaluated first
(quotep ''1) ; but this works
(quotep '(1 2 3))  ; similar to above
(quotep ''(1 2 3)) ; similar to above
(quotep (list 'quote (list 1 2 3))) ; verbose version of previous line

|#

(defun function-symbolp (f)
  (and (symbolp f)
       (not (in f *fo-keywords*))
       (not (keywordp f))
       (not (constant-symbolp f))
       (not (variable-symbolp f))))

#|

(function-symbolp 'c)
(function-symbolp 'c0)
(function-symbolp 'c00)
(function-symbolp 'append)
(function-symbolp '+)

|#

(defmacro mv-and (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a ,b (values nil ,fsig ,rsig)))

(defmacro mv-or (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a (values t ,fsig ,rsig) ,b))

(defun fo-termp (term &optional (fsig nil) (rsig nil))
  (match term
    ((satisfies constant-symbolp) (values t fsig rsig))
    ((satisfies variable-symbolp) (values t fsig rsig))
    ((satisfies quotep) (values t fsig rsig))
    ((satisfies constant-objectp) (values t fsig rsig))
    ((list* f args)
     (mv-and 
      (and (function-symbolp f) (not (get-alist f rsig)))
      (let* ((fsig-arity (get-alist f fsig))
             (acl2s-arity
              (or fsig-arity
                  (acl2s-arity (to-acl2s f))))
             (arity (or acl2s-arity (len args)))
             (fsig (if fsig-arity fsig (acons f arity fsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

(defun fo-termsp (terms fsig rsig)
  (mv-or (endp terms)
         (let+ (((&values res fsig rsig)
                 (fo-termp (car terms) fsig rsig)))
           (mv-and res
                   (fo-termsp (cdr terms) fsig rsig)))))

#|

Examples

(fo-termp '(f d 2))
(fo-termp '(f c 2))
(fo-termp '(f c0 2))
(fo-termp '(f c00 2))
(fo-termp '(f '1 '2))
(fo-termp '(f (f '1 '2)
              (f v1 c1 '2)))


(fo-termp '(binary-append '1 '2))
(fo-termp '(binary-append '1 '2 '3))
(fo-termp '(binary-+ '1 '2))
(fo-termp '(+ '1 '2)) 
(fo-termp '(- '1 '2))

|#

#|

 A FO atomic formula is either an 

 atomic equality: (= t1 t2), where t1, t2 are FO terms.

 atomic relation: (P t1 ... tn), where P is a
 non-constant/non-variable symbol. The arity of P is n and every
 occurrence of (P ...) has to have arity n. Also, if P is a defined
 function in ACL2s, its arity has to match what ACL2s expects.  We do
 not check that if P is a defined function then it has to return a
 Boolean. Make sure that you do not use such examples.

|#

(defun relation-symbolp (f)
  (function-symbolp f))

#|

Examples

(relation-symbolp '<)
(relation-symbolp '<=)
(relation-symbolp 'binary-+)

|#

(defun fo-atomic-formulap (f &optional (fsig nil) (rsig nil))
  (match f
    ((list '= t1 t2)
     (fo-termsp (list t1 t2) fsig rsig))
    ((list* r args)
     (mv-and 
      (and (relation-symbolp r) (not (get-alist r fsig)))
      (let* ((rsig-arity (get-alist r rsig))
             (acl2s-arity
              (or rsig-arity
                  (acl2s::acl2s-arity (to-acl2s r))))
             (arity (or acl2s-arity (len args)))
             (rsig (if rsig-arity rsig (acons r arity rsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a propositional formula. We allow
 Booleans.
 
|#

(defun pfun-fo-argsp (pop args fsig rsig)
  (mv-and (p-funp pop)
          (let ((arity (get-key :arity (get-alist pop *p-ops*))))
            (mv-and (or (== arity '-)
                        (== (len args) arity))
                    (fo-formulasp args fsig rsig)))))

(defun p-fo-formulap (f fsig rsig)
  (match f
    ((type boolean) (values t fsig rsig))
    ((list* pop args)
     (if (p-funp pop)
         (pfun-fo-argsp pop args fsig rsig)
       (values nil fsig rsig)))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a quantified formula. 

 The quantified variables can be a variable 
 or a non-empty list of variables with no duplicates.
 Examples include

 (exists w (P w y z x))
 (exists (w) (P w y z x))
 (forall (x y z) (exists w (P w y z x)))

 But this does not work

 (exists c (P w y z x))
 (forall () (exists w (P w y z x)))
 (forall (x y z x) (exists w (P w y z x)))

|#

(defun quant-fo-formulap (f fsig rsig)
  (match f
    ((list q vars body)
     (mv-and (and (in q *fo-quantifiers*)
                  (or (variable-symbolp vars)
                      (and (consp vars)
                           (no-dupsp vars)
                           (every #'variable-symbolp vars))))
             (fo-formulap body fsig rsig)))
    (_ (values nil fsig rsig))))

(defun mv-seq-first-fun (l)
  (if (endp (cdr l))
      (car l)
    (let ((res (gensym))
          (f (gensym))
          (r (gensym)))
      `(multiple-value-bind (,res ,f ,r)
           ,(car l)
         (if ,res
             (values t ,f ,r)
           ,(mv-seq-first-fun (cdr l)))))))

(defmacro mv-seq-first (&rest rst)
  (mv-seq-first-fun rst))
  
(defun fo-formulap (f &optional (fsig nil) (rsig nil))
  (mv-seq-first
   (fo-atomic-formulap f fsig rsig)
   (p-fo-formulap f fsig rsig)
   (quant-fo-formulap f fsig rsig)
   (values nil fsig rsig)))

(defun fo-formulasp (fs fsig rsig)
  (mv-or (endp fs)
         (let+ (((&values res fsig rsig)
                 (fo-formulap (car fs) fsig rsig)))
           (mv-and res
                   (fo-formulasp (cdr fs) fsig rsig)))))

#|

 We can use fo-formulasp to find the function and relation
 symbols in a formula as follows.
 
|#

(defun fo-f-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car fsig)))

(defun fo-r-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car rsig)))

#|

Examples

(fo-formulap 
 '(forall (x y z) (exists w (P w y z x))))

(fo-formulap 
 '(forall (x y z x) (exists w (P w y z x))))

(quant-fo-formulap 
 '(forall (x y z) (exists y (P w y z x))) nil nil)

(fo-formulap
 '(exists w (P w y z x)))

(fo-atomic-formulap
 '(exists w (P w y z x)) nil nil)

(quant-fo-formulap 
 '(exists w (P w y z x)) nil nil)

(fo-formulap 
 '(P w y z x))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (p1 x1 w) (q c1) (r c2)))
                     (p '2 y w))))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q2 z) (r2 z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall x1 (iff (p1 x1 w) (q c1) (r c2))))

(fo-formulap
 '(iff (p1 x1 w) (q c1) (r c2)))

(fo-atomic-formulap
 '(p1 x1 w))

(variable-symbolp 'c1)
(fo-termp 'x1)
(fo-termp 'w1)
(fo-termp '(x1 w) nil nil)
(fo-termsp '(x1 w) nil nil)

|#

#|
 
 Where appropriate, for the problems below, modify your solutions from
 homework 4. For example, you already implemented most of the
 simplifications in Question 1 in homework 4.
 
|#


#|
 
 Question 1. (25 pts)

 Define function fo-simplify that given a first-order (FO) formula
 returns an equivalent FO formula with the following properties.

 A. The returned formula is either a constant or does not include any
 constants. For example:

 (and (p x) t (q t y) (q y z)) should be simplified to 
 (and (p x) (q t y) (q y z)) 

 (and (p x) t (q t b) nil) should be simplified to nil

 B. Expressions are flattened, e.g.:

 (and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) is not flat, but this is
 (and (p c) (= c '1) (r) (s) (or (r1) (r2)))

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
 form remain (where f is a formula)
 
 (not (not f))

 E. Simplify formulas so that no subexpressions of the following form
 remain 

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or (f) (f1) (p a b) (not (p a b)) (= w z)) should be simplified to 

 t 
 
 F. Simplify formulas so there are no vacuous quantified formulas.
 For example, 

 (forall (x w) (P y z))  should be simplified to
 
 (P y z)

 and 

 (forall (x w) (P x y z))  should be simplified to
 
 (forall (x) (P x y z)) 

 G. Simplify formulas by using ACL2s to evaluate, when possible, terms
 of the form (f ...) where f is an ACL2s function all of whose
 arguments are either constant-objects or quoted objects.

 For example,

 (P (binary-+ 4 2) 3)

 should be simplified to

 (P 6 3)

 Hint: use acl2s-compute and to-acl2s. For example, consider

 (acl2s-compute (to-acl2s '(binary-+ 4 2)))

 On the other hand,

 (P (binary-+ 'a 2) 3)

 does not get simplified because 
 
 (acl2s-compute (to-acl2s '(binary-+ 'a 2)))

 indicates an error (contract/guard violation). See the definition of
 acl2s-compute to see how to determine if an error occurred.

 H. Test your definitions using at least 10 interesting formulas.  Use
 the acl2s code, if you find it useful.  Include deeply nested
 formulas, all of the Boolean operators, quantified formulas, etc.

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
 increase the size of a formula. 

|#

(defun normalize-quant-vars (f)
  (match f
    ((type boolean) f)
    ((satisfies variable-symbolp) f)
    ((satisfies constant-symbolp) f)
    ((satisfies quotep) f)
    ((satisfies constant-objectp) f)
    ((list (and q (or 'forall 'exists)) vars body)
     (let ((vars (if (consp vars) vars (list vars))))
       (list q vars (normalize-quant-vars body))))
    ((cons op args)
     (cons op (mapcar #'normalize-quant-vars args)))
    (_ f)))

(defun free-vars (f)
  (match f
    ((type boolean) nil)
    ((satisfies variable-symbolp) (list f))
    ((satisfies constant-symbolp) nil)
    ((satisfies quotep) nil)
    ((satisfies constant-objectp) nil)
    ((list (or 'forall 'exists) vars body)
     (remove-if (lambda (v) (in v vars)) (free-vars body)))
    ((cons _ args)
     (mapcan #'free-vars args))
    (_ nil)))

(defun complement-of (f)
  (match f
    ((list 'not h) h)
    (_ (list 'not f))))

(defun flatten (op args)
  (mapcan (lambda (a)
            (if (and (consp a) (eq (car a) op))
                (copy-list (cdr a))
                (list a)))
          args))

(defun simplify-not (g)
  (match g
    ((type boolean) (not g))
    ((list 'not h) h)
    (_ (list 'not g))))

(defun simplify-and (args)
  (let ((flat (flatten 'and args))
        (seen (make-hash-table :test 'equal))
        (out  '()))
    (dolist (a flat)
      (cond
        ((eq a t))
        ((eq a nil) (return-from simplify-and nil))
        ((gethash (complement-of a) seen)
         (return-from simplify-and nil))
        ((gethash a seen))
        (t (setf (gethash a seen) t)
           (push a out))))
    (setf out (nreverse out))
    (cond ((null out) t)
          ((null (cdr out)) (car out))
          (t (cons 'and out)))))

(defun simplify-or (args)
  (let ((flat (flatten 'or args))
        (seen (make-hash-table :test 'equal))
        (out  '()))
    (dolist (a flat)
      (cond
        ((eq a nil))
        ((eq a t) (return-from simplify-or t))
        ((gethash (complement-of a) seen)
         (return-from simplify-or t))
        ((gethash a seen))
        (t (setf (gethash a seen) t)
           (push a out))))
    (setf out (nreverse out))
    (cond ((null out) nil)
          ((null (cdr out)) (car out))
          (t (cons 'or out)))))

(defun simplify-implies (p q)
  (cond
    ((eq p nil) t)
    ((eq p t)   q)
    ((eq q t)   t)
    ((eq q nil) (simplify-not p))
    ((equal p q) t)
    ((equal (complement-of p) q) q)
    (t (list 'implies p q))))

(defun simplify-if (c a b)
  (cond
    ((eq c t) a)
    ((eq c nil) b)
    ((equal a b) a)
    ((and (eq a t) (eq b nil)) c)
    ((and (eq a nil) (eq b t)) (simplify-not c))
    ((eq a t) (simplify-or  (list c b)))
    ((eq b nil) (simplify-and (list c a)))
    ((eq a nil) (simplify-and (list (simplify-not c) b)))
    ((eq b t) (simplify-or (list (simplify-not c) a)))
    ((equal a (complement-of b)) (list 'iff c a))
    (t (list 'if c a b))))

(defun simplify-iff (args)
  (let ((flat (flatten 'iff args))
        (polarity t)
        (seen (make-hash-table :test 'equal))
        (out  '()))
    (dolist (a flat)
      (cond
        ((eq a t))
        ((eq a nil) (setf polarity (not polarity)))
        ((gethash (complement-of a) seen)
         (let ((comp (complement-of a)))
           (remhash comp seen)
           (setf out (remove comp out :test #'equal))
           (setf polarity (not polarity))))
        ((gethash a seen)
         (remhash a seen)
         (setf out (remove a out :test #'equal)))
        (t (setf (gethash a seen) t)
           (push a out))))
    (setf out (nreverse out))
    (let ((core (cond ((null out) t)
                      ((null (cdr out)) (car out))
                      (t (cons 'iff out)))))
      (if polarity core (simplify-not core)))))

(defun simplify-quant (q vars body)
  (cond
    ((or (eq body t) (eq body nil)) body)
    (t
     (let* ((fv   (free-vars body))
            (kept (remove-if-not (lambda (v) (in v fv)) vars)))
       (cond
         ((null kept) body)
         ((and (consp body) (eq (car body) q))
          (list q (append kept (cadr body)) (caddr body)))
         (t (list q kept body)))))))

(defun ground-argp (a)
  (or (constant-objectp a) (quotep a)))

(defun all-ground-args (args)
  (every #'ground-argp args))

(defun quote-result (v)
  (cond
    ((booleanp v) v)
    ((constant-objectp v) v)
    (t (list 'quote v))))

(defun try-eval (f)
  (match f
    ((cons head args)
     (if (and (symbolp head)
              (not (in head *p-funs*))
              (not (in head *fo-quantifiers*))
              (not (eq head 'quote))
              (all-ground-args args)
              (or (eq head '=) (acl2s-arity (to-acl2s head))))
         (let* ((res (acl2s-compute (to-acl2s f)))
                (err (car res))
                (val (cadr res)))
           (if err f (quote-result val)))
         f))
    (_ f)))

(defun fo-simplify (f)
  (fo-simplify-aux (normalize-quant-vars f)))

(defun fo-simplify-aux (f)
  (match f
    ((type boolean) f)
    ((satisfies variable-symbolp) f)
    ((satisfies constant-symbolp) f)
    ((satisfies quotep) f)
    ((satisfies constant-objectp) f)
    ((list 'not g) (simplify-not (fo-simplify-aux g)))
    ((list 'implies p q)
     (simplify-implies (fo-simplify-aux p) (fo-simplify-aux q)))
    ((list 'if c a b)
     (simplify-if (fo-simplify-aux c) (fo-simplify-aux a) (fo-simplify-aux b)))
    ((cons 'and args) (simplify-and (mapcar #'fo-simplify-aux args)))
    ((cons 'or args)  (simplify-or  (mapcar #'fo-simplify-aux args)))
    ((cons 'iff args) (simplify-iff (mapcar #'fo-simplify-aux args)))
    ((list (and q (or 'forall 'exists)) vars body)
     (simplify-quant q vars (fo-simplify-aux body)))
    ((list '= t1 t2)
     (try-eval (list '= (fo-simplify-term t1) (fo-simplify-term t2))))
    ((cons r args)
     (try-eval (cons r (mapcar #'fo-simplify-term args))))
    (_ f)))

(defun fo-simplify-term (tm)
  (match tm
    ((type boolean) tm)
    ((satisfies variable-symbolp) tm)
    ((satisfies constant-symbolp) tm)
    ((satisfies quotep) tm)
    ((satisfies constant-objectp) tm)
    ((cons f args)
     (try-eval (cons f (mapcar #'fo-simplify-term args))))
    (_ tm)))

;; Q1 tests
(fo-simplify 't)
(fo-simplify '(and (P x) t (Q y)))
(fo-simplify '(and (P x) nil (Q y)))
(fo-simplify '(or (P x) t (Q y)))
(fo-simplify '(and (P x) (and (Q y) (R z))))
(fo-simplify '(not (not (not (P x)))))
(fo-simplify '(or (f) (f1) (p a b) (not (p a b)) (= w z)))
(fo-simplify '(forall (x w) (P y z)))
(fo-simplify '(forall (x w) (P x y z)))
(fo-simplify '(P (binary-+ 4 2) 3))
(fo-simplify '(P (binary-+ 'a 2) 3))

#|

 Question 2. (10 pts)

 Define nnf, a function that given a FO formula, something that
 satisfies fo-formulap, puts it into negation normal form (NNF).

 The resulting formula cannot contain any of the following
 propositional connectives: implies, iff, if.

 Test nnf using at least 10 interesting formulas. Make sure you
 support quantification.

|#

(defun nnf (f) (nnf-aux f t))

(defun nnf-aux (f pos)
  (match f
    ((type boolean) (if pos f (not f)))
    ((list 'not g) (nnf-aux g (not pos)))
    ((cons 'and args)
     (cons (if pos 'and 'or)
           (mapcar (lambda (a) (nnf-aux a pos)) args)))
    ((cons 'or args)
     (cons (if pos 'or 'and)
           (mapcar (lambda (a) (nnf-aux a pos)) args)))
    ((list 'implies p q)
     (if pos
         (list 'or  (nnf-aux p (not pos)) (nnf-aux q pos))
         (list 'and (nnf-aux p (not pos)) (nnf-aux q pos))))
    ((list 'if c a b)
     (if pos
         (list 'or
               (list 'and (nnf-aux c t)   (nnf-aux a t))
               (list 'and (nnf-aux c nil) (nnf-aux b t)))
         (list 'and
               (list 'or  (nnf-aux c nil) (nnf-aux a nil))
               (list 'or  (nnf-aux c t)   (nnf-aux b nil)))))
    ((cons 'iff args) (nnf-iff args pos))
    ((list (and q (or 'forall 'exists)) vars body)
     (let ((new-q (if pos q (if (eq q 'forall) 'exists 'forall))))
       (list new-q vars (nnf-aux body pos))))
    (_ (if pos f (list 'not f)))))

(defun nnf-iff (args pos)
  (cond
    ((endp args) (if pos t nil))
    ((endp (cdr args)) (nnf-aux (car args) pos))
    ((endp (cddr args)) (nnf-iff-binary (car args) (cadr args) pos))
    (t
     (let ((pairs '()))
       (do ((l args (cdr l))) ((endp (cdr l)))
         (push (nnf-iff-binary (car l) (cadr l) t) pairs))
       (nnf-aux (cons 'and (nreverse pairs)) pos)))))

(defun nnf-iff-binary (p q pos)
  (if pos
      (list 'or
            (list 'and (nnf-aux p t)   (nnf-aux q t))
            (list 'and (nnf-aux p nil) (nnf-aux q nil)))
      (list 'and
            (list 'or  (nnf-aux p t)   (nnf-aux q t))
            (list 'or  (nnf-aux p nil) (nnf-aux q nil)))))

;; Q2 tests
(nnf '(implies (P x) (Q y)))
(nnf '(not (implies (P x) (Q y))))
(nnf '(iff (P x) (Q y)))
(nnf '(not (iff (P x) (Q y))))
(nnf '(if (R z) (P x) (Q y)))
(nnf '(not (forall (x) (P x))))
(nnf '(forall (x) (implies (P x) (exists (y) (Q x y)))))
(nnf '(not (and (P x) (or (Q y) (not (R z))))))
(nnf '(iff (P x) (Q y) (R z)))
(nnf '(not (exists (x) (forall (y) (implies (P x y) (Q y))))))

#|

 Question 3. (25 pts)

 Define simp-skolem-pnf-cnf, a function that given a FO formula,
 simplifies it using fo-simplify, then puts it into negation normal
 form, applies skolemization, then puts the formula in prenex normal
 form and finally transforms the matrix into an equivalent CNF
 formula.

 To be clear: The formula returned should be equi-satisfiable with the
 input formula, should contain no existential quantifiers, and if it
 has quantifiers it should be of the form

 (forall (...) matrix)

 where matrix is quantifier-free and in CNF. 

 The fewer quantified variables, the better.
 The fewer Skolem functions, the better.
 The smaller the arity of Skolem functions, the better.
 Having said that, correctness should be your primary consideration.

 Test your functions using at least 10 interesting formulas. 
 
|#

;; =====================================================================
;; Q3: simp-skolem-pnf-cnf (distributive CNF, no Tseitin)
;; =====================================================================

(defun substitute-vars (f subst)
  (match f
    ((type boolean) f)
    ((satisfies variable-symbolp)
     (let ((pair (assoc f subst :test #'eq)))
       (if pair (cdr pair) f)))
    ((satisfies constant-symbolp) f)
    ((satisfies quotep) f)
    ((satisfies constant-objectp) f)
    ((list (and q (or 'forall 'exists)) vars body)
     (list q vars (substitute-vars body subst)))
    ((cons op args)
     (cons op (mapcar (lambda (a) (substitute-vars a subst)) args)))
    (_ f)))

(defun rename-apart (f subst)
  (match f
    ((type boolean) f)
    ((satisfies variable-symbolp)
     (let ((pair (assoc f subst :test #'eq)))
       (if pair (cdr pair) f)))
    ((satisfies constant-symbolp) f)
    ((satisfies quotep) f)
    ((satisfies constant-objectp) f)
    ((list (and q (or 'forall 'exists)) vars body)
     (let* ((fresh    (mapcar (lambda (v)
                                (declare (ignore v))
                                (gentemp "X"))
                              vars))
            (new-subst (nconc (mapcar #'cons vars fresh) subst)))
       (list q fresh (rename-apart body new-subst))))
    ((cons op args)
     (cons op (mapcar (lambda (a) (rename-apart a subst)) args)))
    (_ f)))

(defun make-skolem-term (args)
  (if (endp args)
      (gentemp "C")
      (cons (gentemp "SK") args)))

(defun skolemize (f univs)
  (match f
    ((type boolean) f)
    ((satisfies variable-symbolp) f)
    ((satisfies constant-symbolp) f)
    ((satisfies quotep) f)
    ((satisfies constant-objectp) f)
    ((list 'forall vars body)
     (list 'forall vars (skolemize body (append univs vars))))
    ((list 'exists vars body)
     (let* ((fv      (free-vars body))
            (needed  (remove-if-not (lambda (u) (in u fv)) univs))
            (subst   (mapcar (lambda (v) (cons v (make-skolem-term needed)))
                             vars))
            (body2   (substitute-vars body subst)))
       (skolemize body2 univs)))
    ((cons op args)
     (cons op (mapcar (lambda (a) (skolemize a univs)) args)))
    (_ f)))

(defun pnf (f)
  (match f
    ((type boolean) f)
    ((satisfies variable-symbolp) f)
    ((satisfies constant-symbolp) f)
    ((satisfies quotep) f)
    ((satisfies constant-objectp) f)
    ((list 'not g) (list 'not (pnf g)))
    ((list 'forall vars body)
     (let ((body2 (pnf body)))
       (match body2
         ((list 'forall inner-vars inner-body)
          (list 'forall (append vars inner-vars) inner-body))
         (_ (list 'forall vars body2)))))
    ((cons op args)
     (if (in op '(and or))
         (let* ((pargs    (mapcar #'pnf args))
                (all-vars '())
                (stripped (mapcar (lambda (a)
                                    (match a
                                      ((list 'forall vs body)
                                       (setf all-vars (append all-vars vs))
                                       body)
                                      (_ a)))
                                  pargs)))
           (if (null all-vars)
               (cons op stripped)
               (list 'forall all-vars (cons op stripped))))
         (cons op args)))
    (_ f)))

(defun conjuncts-of (f)
  (match f
    ((cons 'and args) args)
    (_ (list f))))

(defun disjuncts-of (f)
  (match f
    ((cons 'or args) args)
    (_ (list f))))

(defun cartesian-product (lists)
  (cond
    ((endp lists) (list nil))
    (t (let ((rest (cartesian-product (cdr lists))))
         (mapcan (lambda (elt)
                   (mapcar (lambda (tup) (cons elt tup)) rest))
                 (car lists))))))

(defun cnf-distribute (cnf-args)
  (let* ((conj-sets (mapcar #'conjuncts-of cnf-args))
         (tuples    (cartesian-product conj-sets))
         (disjuncts (mapcar
                     (lambda (tuple)
                       (simplify-or (mapcan #'disjuncts-of tuple)))
                     tuples)))
    (simplify-and disjuncts)))

(defun matrix-to-cnf (f)
  (match f
    ((type boolean) f)
    ((list 'not _) f)
    ((cons 'and args)
     (simplify-and (mapcan (lambda (a)
                             (let ((ca (matrix-to-cnf a)))
                               (if (and (consp ca) (eq (car ca) 'and))
                                   (copy-list (cdr ca))
                                   (list ca))))
                           args)))
    ((cons 'or args)
     (cnf-distribute (mapcar #'matrix-to-cnf args)))
    (_ f)))

(defun pnf-to-cnf (f)
  (match f
    ((list 'forall vars body)
     (list 'forall vars (matrix-to-cnf body)))
    (_ (matrix-to-cnf f))))

(defun simp-skolem-pnf-cnf (f)
  (let ((g (fo-simplify f)))
    (cond
      ((or (eq g t) (eq g nil)) g)
      (t (let* ((n (nnf g))
                (r (rename-apart n nil))
                (s (skolemize r nil))
                (p (pnf s))
                (c (pnf-to-cnf p)))
           c)))))
;; Q3 tests
(simp-skolem-pnf-cnf '(P x))
(simp-skolem-pnf-cnf '(implies (P x) (Q x)))
(simp-skolem-pnf-cnf '(forall (x) (P x)))
(simp-skolem-pnf-cnf '(exists (x) (P x)))
(simp-skolem-pnf-cnf '(forall (x) (exists (y) (P x y))))
(simp-skolem-pnf-cnf '(and (forall (x) (P x)) (forall (x) (Q x))))
(simp-skolem-pnf-cnf '(implies (forall (x) (P x)) (exists (y) (Q y))))
(simp-skolem-pnf-cnf '(forall (x) (or (P x) (and (Q x) (R x)))))
(simp-skolem-pnf-cnf '(exists (x) (forall (y) (P x y))))
(simp-skolem-pnf-cnf '(forall (x) (exists (y) (forall (z) (P x y z)))))
(simp-skolem-pnf-cnf '(iff (P x) (Q x)))

#|

 Question 4. (15 pts)

 Define unify, a function that given an a non-empty list of pairs,
 where every element of the pair is FO-term, returns an mgu (most
 general unifier) if one exists or the symbol 'fail otherwise.

 An assignment is a list of conses, where car is a variable, the cdr
 is a term and the variables (in the cars) are unique.

 Test your functions using at least 10 interesting inputs. 
 
|#

(defun unify (eqs)
  (unify-aux (mapcar (lambda (p) (cons (car p) (cadr p))) eqs) nil))

(defun unify-aux (eqs subst)
  (cond
    ((endp eqs) subst)
    (t
     (let* ((eq (car eqs)) (s (car eq)) (r (cdr eq)) (rest (cdr eqs)))
       (cond
         ((equal s r) (unify-aux rest subst))
         ((and (not (variable-symbolp s)) (variable-symbolp r))
          (unify-aux (cons (cons r s) rest) subst))
         ((variable-symbolp s)
          (if (occurs-in s r)
              'fail
              (unify-aux (subst-in-eqs s r rest)
                         (cons (cons s r) (subst-in-subst s r subst)))))
         ((or (constant-symbolp s) (constant-symbolp r)
              (quotep s) (quotep r)
              (constant-objectp s) (constant-objectp r))
          'fail)
         ((and (consp s) (consp r)
               (eq (car s) (car r))
               (== (len (cdr s)) (len (cdr r))))
          (unify-aux (append (pairlis (cdr s) (cdr r)) rest) subst))
         (t 'fail))))))

(defun occurs-in (x tm)
  (match tm
    ((satisfies variable-symbolp) (eq x tm))
    ((cons _ args) (some (lambda (a) (occurs-in x a)) args))
    (_ nil)))

(defun subst-in-term (x tm term)
  (match term
    ((satisfies variable-symbolp) (if (eq x term) tm term))
    ((satisfies constant-symbolp) term)
    ((satisfies quotep) term)
    ((satisfies constant-objectp) term)
    ((cons f args) (cons f (mapcar (lambda (a) (subst-in-term x tm a)) args)))
    (_ term)))

(defun subst-in-eqs (x tm eqs)
  (mapcar (lambda (p)
            (cons (subst-in-term x tm (car p))
                  (subst-in-term x tm (cdr p))))
          eqs))

(defun subst-in-subst (x tm subst)
  (mapcar (lambda (p) (cons (car p) (subst-in-term x tm (cdr p)))) subst))

;; Q4 tests
(unify '((x 1)))
(unify '((1 x)))
(unify '((x x)))
(unify '((c1 c2)))
(unify '((x '(a b))))
(unify '(((f x 2) (f 1 y))))
(unify '(((f x y) (f y x))))
(unify '(((f x) (g x))))
(unify '((x (f x))))
(unify '((x y) (y z) (z 1)))
(unify '(((f x x) (f y (g y)))))
(unify '(((f x (g y)) (f (g z) (g w)))))
#|

 Question 5. (25 pts)

 Define fo-no=-val, a function that given a FO formula, without equality,
 checks if it is valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement.

 Test your functions using at least 10 interesting inputs
 including the formulas from the following pages of the book: 178
 (p38, p34), 179 (ewd1062), 180 (barb), and 198 (the Los formula).


|#

;; =====================================================================
;; Q5: fo-no=-val — optimized resolution
;; =====================================================================

(defparameter *canon-counter* 0)

(defun canonical-rename (clause)
  (let ((subst '())
        (counter 0))
    (labels ((walk-term (tm)
               (cond
                 ((variable-symbolp tm)
                  (let ((pair (assoc tm subst :test #'eq)))
                    (cond
                      (pair (cdr pair))
                      (t (let ((fresh (intern (format nil "CVAR~a" (incf counter)))))
                           (setf subst (cons (cons tm fresh) subst))
                           fresh)))))
                 ((atom tm) tm)
                 (t (cons (car tm) (mapcar #'walk-term (cdr tm))))))
             (walk-lit (lit)
               (match lit
                 ((list 'not a) (list 'not (walk-term a)))
                 (_ (walk-term lit)))))
      (mapcar #'walk-lit clause))))

;; ---- Literal and clause helpers (shared with Q5 framework) ----

(defun literal-atomp (lit)
  (match lit
    ((list 'not _) nil)
    (_ t)))

(defun literal-negate (lit)
  (match lit
    ((list 'not a) a)
    (_ (list 'not lit))))

(defun atom-of (lit)
  (match lit
    ((list 'not a) a)
    (_ lit)))

(defun positive-clausep (clause)
  (every #'literal-atomp clause))

(defun tautologyp (clause)
  (some (lambda (lit) (member (literal-negate lit) clause :test #'equal))
        clause))

(defun strip-forall (f)
  (match f
    ((list 'forall _ body) body)
    (_ f)))

(defun literals-of (clause)
  (match clause
    ((cons 'or args) args)
    (_ (list clause))))

(defun clauses-of (matrix)
  (match matrix
    ((type boolean) (if matrix '() (list '())))
    ((cons 'and args) (mapcar #'literals-of args))
    (_ (list (literals-of matrix)))))

;; ---- Matching (one-sided, for subsumption) ----

(defun match-term (pattern target subst)
  (cond
    ((variable-symbolp pattern)
     (let ((pair (assoc pattern subst :test #'eq)))
       (cond
         (pair (if (equal (cdr pair) target) subst 'fail))
         (t (cons (cons pattern target) subst)))))
    ((equal pattern target) subst)
    ((and (consp pattern) (consp target)
          (eq (car pattern) (car target))
          (== (len (cdr pattern)) (len (cdr target))))
     (match-terms (cdr pattern) (cdr target) subst))
    (t 'fail)))

(defun match-terms (ps ts subst)
  (cond
    ((and (endp ps) (endp ts)) subst)
    ((or (endp ps) (endp ts)) 'fail)
    (t (let ((s (match-term (car ps) (car ts) subst)))
         (if (eq s 'fail) 'fail (match-terms (cdr ps) (cdr ts) s))))))

(defun match-literal (pat-lit tgt-lit subst)
  (cond
    ((and (literal-atomp pat-lit) (literal-atomp tgt-lit))
     (match-term pat-lit tgt-lit subst))
    ((and (not (literal-atomp pat-lit)) (not (literal-atomp tgt-lit)))
     (match-term (atom-of pat-lit) (atom-of tgt-lit) subst))
    (t 'fail)))

(defun subsumes-p (c d)
  (subsumes-aux c d nil))

(defun subsumes-aux (c d subst)
  (cond
    ((endp c) t)
    (t
     (let ((lit (car c)) (rest (cdr c)))
       (some (lambda (d-lit)
               (let ((unif (match-literal lit d-lit subst)))
                 (and (not (eq unif 'fail))
                      (subsumes-aux rest d unif))))
             d)))))

;; ---- Substitution on clauses ----

(defun apply-subst-term (subst tm)
  (match tm
    ((satisfies variable-symbolp)
     (let ((pair (assoc tm subst :test #'eq)))
       (if pair (cdr pair) tm)))
    ((satisfies constant-symbolp) tm)
    ((satisfies quotep) tm)
    ((satisfies constant-objectp) tm)
    ((cons f args) (cons f (mapcar (lambda (a) (apply-subst-term subst a)) args)))
    (_ tm)))

(defun apply-subst-literal (subst lit)
  (match lit
    ((list 'not a) (list 'not (apply-subst-term subst a)))
    (_ (apply-subst-term subst lit))))

(defun apply-subst-clause (subst clause)
  (remove-duplicates
   (mapcar (lambda (l) (apply-subst-literal subst l)) clause)
   :test #'equal))

(defun clause-vars (clause)
  (remove-duplicates
   (mapcan (lambda (lit) (free-vars (atom-of lit))) clause)
   :test #'eq))

(defun standardize-apart-clause (clause)
  (let* ((vars (clause-vars clause))
         (fresh (mapcar (lambda (v) (declare (ignore v)) (gentemp "X")) vars))
         (alist (mapcar #'cons vars fresh)))
    (apply-subst-clause alist clause)))

;; ---- Resolution primitive ----

(defun resolvents-between (pos-parent other-parent)
  (let ((results '()))
    (dolist (p-lit pos-parent)
      (dolist (o-lit other-parent)
        (unless (literal-atomp o-lit)
          (let* ((p-atom (atom-of p-lit))
                 (o-atom (atom-of o-lit))
                 (mgu    (unify (list (list p-atom o-atom)))))
            (unless (eq mgu 'fail)
              (let* ((residual-pos (remove p-lit pos-parent :test #'equal :count 1))
                     (residual-oth (remove o-lit other-parent :test #'equal :count 1))
                     (combined     (append residual-pos residual-oth))
                     (after-subst  (apply-subst-clause mgu combined)))
                (push after-subst results)))))))
    results))

;; ---- Factoring ----

(defun factor-clause (clause)
  (let ((factors '())
        (vec (coerce clause 'vector))
        (n (length clause)))
    (loop for i from 0 below n do
      (loop for j from (1+ i) below n do
        (let ((li (aref vec i)) (lj (aref vec j)))
          (when (eq (literal-atomp li) (literal-atomp lj))
            (let ((mgu (unify (list (list (atom-of li) (atom-of lj))))))
              (unless (eq mgu 'fail)
                (push (apply-subst-clause mgu clause) factors)))))))
    factors))

;; ---- Clause weight / canonicalization ----

(defun clause-weight (clause)
  "Unit preference: unit clauses get weight 0, others get size + depth penalty."
  (cond
    ((endp (cdr clause)) 0)               ; unit clause — highest priority
    (t
     (let ((size 0))
       (labels ((walk (x)
                  (cond
                    ((atom x) (incf size))
                    (t (incf size) (dolist (c x) (walk c))))))
         (dolist (lit clause) (walk lit)))
       (+ size (* 2 (clause-max-depth clause)))))))

(defun canonicalize-clause (clause)
  "Sort literals by sxhash for stable equality comparison across
   structurally-equal clauses with different literal orderings."
  (sort (copy-list clause)
        (lambda (a b) (< (sxhash a) (sxhash b)))))

(defparameter *max-clause-literals* 15)
(defparameter *max-term-depth* 6)

(defun term-depth (tm)
  (cond
    ((atom tm) 0)
    ((and (consp tm) (eq (car tm) 'quote)) 0)
    (t (1+ (reduce #'max (mapcar #'term-depth (cdr tm))
                   :initial-value 0)))))

(defun literal-depth (lit)
  (match lit
    ((list 'not a) (term-depth a))
    (_ (term-depth lit))))

(defun clause-max-depth (clause)
  (reduce #'max (mapcar #'literal-depth clause) :initial-value 0))


;; ---- Indexing for fast subsumption ----
;;
;; For each clause we precompute: the multiset of predicate symbols
;; with their polarities. A necessary condition for C to subsume D is
;; that C's predicate-polarity multiset is a submultiset of D's. This
;; is a cheap filter that avoids most subsumption calls.

(defun literal-signature (lit)
  "(predicate . polarity) where polarity is t for positive, nil for negative."
  (match lit
    ((list 'not a) (cons (if (consp a) (car a) a) nil))
    (_ (cons (if (consp lit) (car lit) lit) t))))

(defun clause-signature (clause)
  "Sorted list of (pred . polarity) pairs — the polarity multiset."
  (sort (mapcar #'literal-signature clause)
        (lambda (a b) (string< (symbol-name (or (car a) '|nil|))
                               (symbol-name (or (car b) '|nil|))))))

(defun sig-submultiset-p (sig-c sig-d)
  "Is sig-c a submultiset of sig-d? Both are sorted lists of (pred . pol)."
  (cond
    ((endp sig-c) t)
    ((endp sig-d) nil)
    ((equal (car sig-c) (car sig-d))
     (sig-submultiset-p (cdr sig-c) (cdr sig-d)))
    ((let ((a (car sig-c)) (b (car sig-d)))
       (or (string< (symbol-name (or (car b) '|nil|))
                    (symbol-name (or (car a) '|nil|)))
           (and (equal (car a) (car b)) (not (eq (cdr a) (cdr b))))))
     (sig-submultiset-p sig-c (cdr sig-d)))
    (t (sig-submultiset-p sig-c (cdr sig-d)))))

;; Structure: bundle a clause with its precomputed sig and canonical form.

(defstruct cl literals canon sig weight)

(defun build-cl (literals)
  (let* ((renamed (canonical-rename literals))
         (can (sort (copy-list renamed)
                    (lambda (a b) (< (sxhash a) (sxhash b))))))
    (make-cl :literals literals
             :canon can
             :sig (clause-signature literals)
             :weight (clause-weight literals))))

(defun cl-subsumes-p (c d)
  "Fast subsumption with signature pre-filter."
  (and (sig-submultiset-p (cl-sig c) (cl-sig d))
       (subsumes-p (cl-literals c) (cl-literals d))))

(defun cl-equal (c d)
  (equal (cl-canon c) (cl-canon d)))

(defun cl-tautologyp (c) (tautologyp (cl-literals c)))

;; ---- Resolution ----

(defun try-resolve-cl (c1 c2)
  "Resolve two cl structs; return list of new clause-lists (raw literal lists)."
  (let* ((c1-lits (cl-literals c1))
         (c2-lits (cl-literals c2))
         (c1-vars (clause-vars c1-lits))
         (c2-vars (clause-vars c2-lits))
         (c2-eff (if (intersection c1-vars c2-vars :test #'eq)
                     (standardize-apart-clause c2-lits)
                     c2-lits))
         (results '()))
    (when (positive-clausep c1-lits)
      (setf results (nconc (resolvents-between c1-lits c2-eff) results)))
    (when (positive-clausep c2-eff)
      (setf results (nconc (resolvents-between c2-eff c1-lits) results)))
    results))

(defun factor-clause-cl (c)
  (factor-clause (cl-literals c)))

;; ---- Index: group clauses by head-predicate of positive literals ----
;;
;; For positive resolution, we need one all-positive parent. We keep
;; positive clauses indexed by the predicates they contain, so that
;; given a negative literal (P ...), we can find candidate positive
;; parents quickly.

(defparameter *pos-clause-index* (make-hash-table :test 'eq))
(defparameter *all-clauses* nil)
(defparameter *clause-set-hash* (make-hash-table :test 'equal))

(defun reset-index ()
  (setf *pos-clause-index* (make-hash-table :test 'eq))
  (setf *all-clauses* nil)
  (setf *clause-set-hash* (make-hash-table :test 'equal)))

(defun index-add (c)
  (setf (gethash (cl-canon c) *clause-set-hash*) c)
  (push c *all-clauses*)
  (when (positive-clausep (cl-literals c))
    (dolist (lit (cl-literals c))
      (let ((pred (car (literal-signature lit))))
        (push c (gethash pred *pos-clause-index* '()))))))

(defun index-remove (c)
  (remhash (cl-canon c) *clause-set-hash*)
  (setf *all-clauses* (delete c *all-clauses* :test #'eq))
  (when (positive-clausep (cl-literals c))
    (dolist (lit (cl-literals c))
      (let ((pred (car (literal-signature lit))))
        (setf (gethash pred *pos-clause-index*)
              (delete c (gethash pred *pos-clause-index* '())
                      :test #'eq))))))

(defun index-candidates-for (c)
  "Given a clause c, return candidate resolution partners from the index.
   Union of (positive clauses sharing a predicate with any negative literal of c),
   plus (c itself, since c might be positive and we resolve it against any clause)."
  (let ((candidates (make-hash-table :test 'eq)))
    ;; If c has a negative literal (P ...), any positive clause containing P
    ;; mentioning the same polarity is a candidate.
    (dolist (lit (cl-literals c))
      (unless (literal-atomp lit)
        (let ((pred (car (literal-signature lit))))
          (dolist (p (gethash pred *pos-clause-index* '()))
            (setf (gethash p candidates) t)))))
    ;; If c itself is positive, any clause containing a matching negative
    ;; literal is a candidate. Pull from all-clauses filtered by predicate.
    (when (positive-clausep (cl-literals c))
      (dolist (lit (cl-literals c))
        (let ((pred (car (literal-signature lit))))
          (dolist (other *all-clauses*)
            (dolist (olit (cl-literals other))
              (when (and (not (literal-atomp olit))
                         (eq pred (car (literal-signature olit))))
                (setf (gethash other candidates) t)))))))
    (let ((result '()))
      (maphash (lambda (k v) (declare (ignore v)) (push k result)) candidates)
      result)))

;; ---- Priority queue by weight ----

(defparameter *passive* nil)

(defun passive-insert (c)
  "Insert into passive list keyed by weight (simple sorted insertion)."
  (cond
    ((endp *passive*)
     (setf *passive* (list c)))
    ((< (cl-weight c) (cl-weight (car *passive*)))
     (setf *passive* (cons c *passive*)))
    (t
     (let ((prev *passive*)
           (curr (cdr *passive*)))
       (loop while (and curr (>= (cl-weight c) (cl-weight (car curr)))) do
         (setf prev curr) (setf curr (cdr curr)))
       (setf (cdr prev) (cons c curr))))))

(defun passive-pop ()
  (when *passive*
    (let ((c (car *passive*)))
      (setf *passive* (cdr *passive*))
      c)))

;; ---- Integration of new clauses ----

(defun clause-exists-exact-p (c)
  (gethash (cl-canon c) *clause-set-hash*))

(defun subsumed-by-any-p (c)
  "Is c subsumed by any clause in the index? Uses signature filter."
  (some (lambda (d) (cl-subsumes-p d c)) *all-clauses*))

(defun remove-subsumed-by (c)
  "Remove from index any clause subsumed by c."
  (let ((to-remove '()))
    (dolist (d *all-clauses*)
      (when (and (not (eq c d)) (cl-subsumes-p c d))
        (push d to-remove)))
    (dolist (d to-remove) (index-remove d))
    ;; Also clean up passive
    (setf *passive* (remove-if (lambda (d) (find d to-remove :test #'eq)) *passive*))))

(defun try-add-clause (lits)
  (cond
    ((endp lits) t)
    ((tautologyp lits) nil)
    ((> (length lits) *max-clause-literals*) nil)
    ((> (clause-max-depth lits) *max-term-depth*) nil)
    (t
     (let ((c (build-cl lits)))
       (cond
         ((clause-exists-exact-p c) nil)
         ((subsumed-by-any-p c) nil)
         (t
          (remove-subsumed-by c)
          (index-add c)
          (passive-insert c)
          nil))))))

;; ---- Main saturation loop ----

(defparameter *max-iters* 10000)
(defparameter *print-every* 100)

(defun saturate ()
  (let ((iter 0))
    (loop
      (when (and (plusp *print-every*) (zerop (mod iter *print-every*)))
        (format t "~&iter=~a |index|=~a |passive|=~a~%"
                iter (length *all-clauses*) (length *passive*))
        (finish-output))
      (when (> iter *max-iters*)
        (format t "~&Hit max-iters limit (~a)~%" *max-iters*)
        (return nil))
      (incf iter)
      (let ((given (passive-pop)))
        (cond
          ((null given) (return nil))
          (t
           (dolist (fact (factor-clause-cl given))
             (when (try-add-clause fact)
               (return-from saturate t)))
           (dolist (partner (index-candidates-for given))
             (dolist (res (try-resolve-cl given partner))
               (when (try-add-clause res)
                 (return-from saturate t))))))))))

;; ---- Top-level ----

(defun fo-no=-val (f)
  (reset-index)
  (setf *passive* nil)
  (let* ((negated-f   (list 'not f))
         (cnf-formula (simp-skolem-pnf-cnf negated-f)))
    (cond
      ((eq cnf-formula nil) 'valid)
      ((eq cnf-formula t)   nil)
      (t
       (let* ((matrix  (strip-forall cnf-formula))
              (clauses (clauses-of matrix)))
         (dolist (c clauses)
           (when (try-add-clause c) (return-from fo-no=-val 'valid)))
         (if (saturate) 'valid nil))))))

;; ---- Q5 tests ----

;; Propositional
(fo-no=-val '(or (P c1) (not (P c1))))
(fo-no=-val '(implies (P c1) (P c1)))
(fo-no=-val '(implies (and (P c1) (Q c1)) (P c1)))
(fo-no=-val '(implies (and (implies (P c1) (Q c1)) (P c1)) (Q c1)))
(fo-no=-val '(iff (implies (P c1) (Q c1))
                  (implies (not (Q c1)) (not (P c1)))))
(fo-no=-val '(or (P c1) (Q c1)))
(fo-no=-val '(implies (and (implies (P c1) (Q c1)) (Q c1)) (P c1)))

;; Quantified
(fo-no=-val '(implies (forall (x) (P x)) (P c1)))
(fo-no=-val '(implies (P c1) (exists (x) (P x))))
(fo-no=-val '(implies (exists (x) (forall (y) (P x y)))
                      (forall (y) (exists (x) (P x y)))))
(fo-no=-val '(implies (forall (y) (exists (x) (P x y)))
                      (exists (x) (forall (y) (P x y)))))

;; Textbook: barber (p180)
(fo-no=-val
 '(not (exists (x)
         (forall (y)
           (iff (shaves x y)
                (not (shaves y y)))))))

;; Textbook: p38 (p178)
(fo-no=-val
 '(iff (forall (x)
         (implies (and (P ca)
                       (implies (P x)
                                (exists (y) (and (P y) (R x y)))))
                  (exists (z w)
                          (and (P z) (R x w) (R w z)))))
       (forall (x)
         (and (or (not (P ca))
                  (P x)
                  (exists (z w)
                          (and (P z) (R x w) (R w z))))
              (or (not (P ca))
                  (not (exists (y) (and (P y) (R x y))))
                  (exists (z w)
                          (and (P z) (R x w) (R w z))))))))

;; Textbook: EWD1062 (p179)
(fo-no=-val
 '(implies
   (and (forall (x) (leq x x))
        (forall (x y z) (implies (and (leq x y) (leq y z)) (leq x z)))
        (forall (x y) (iff (leq (f x) y) (leq x (g y)))))
   (and (forall (x y) (implies (leq x y) (leq (f x) (f y))))
        (forall (x y) (implies (leq x y) (leq (g x) (g y)))))))

;; Textbook: Los (p198)
(fo-no=-val
 '(implies
   (and (forall (x y z) (implies (and (P x y) (P y z)) (P x z)))
        (forall (x y z) (implies (and (Q x y) (Q y z)) (Q x z)))
        (forall (x y) (implies (Q x y) (Q y x)))
        (forall (x y) (or (P x y) (Q x y))))
   (or (forall (x y) (P x y))
       (forall (x y) (Q x y)))))

;; Textbook: p34 (p178)
(fo-no=-val
 '(iff (iff (exists (x) (forall (y) (iff (P x) (P y))))
            (iff (exists (x) (Q x))
                 (forall (y) (Q y))))
       (iff (exists (x) (forall (y) (iff (Q x) (Q y))))
            (iff (exists (x) (P x))
                 (forall (y) (P y))))))


#|

 Question 6. Extra Credit (20 pts)

 Define fo-val, a function that given a FO formula, checks if it is
 valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement. This is an extension of question 5,
 where you replace equality with a new relation symbol and add
 the appropriate equivalence and congruence hypotheses.

|#

(defun fo-val (f) ...)
