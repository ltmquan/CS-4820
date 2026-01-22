#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Spring 2026

 Homework 2.
 Due: 1/26 (Midnight)

 For this assignment, work in groups of 1-2.

 Send me a link to your repo and cc the grader and your group members.
 Send only 1 email per group and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 2". Also, your
 repo should have this file in it with solutions/answers included.

 The group members are:
 Quan Luu

|#

#|

 In this homework, we will explore the distinction between meta and
 object languages. See pg. 11 of the Harrison book.

 Here is a little story to set the context. In CS2800 and, briefly, in
 this class, we reviewed the syntax and semantics of the ACL2s
 language. What language did we use to do that? English. Technically,
 we would say that English is the metalanguage used to study the
 object language ACL2s. Notice "object" here has nothing to do with
 objects from object-oriented languages. More accurately, we might say
 mathematical English or CS English is the metalanguage, as fields
 such as mathematics and CS use a version of English better suited for
 their purposes, eg, in CS English, words like "implies," "tree,"
 "induction" and "reasoning" have special meanings.
 
 Mathematical English is not a formal language, hence, just like
 English, it is ambiguous (though not to the same extent) and one can
 take many shortcuts in describing things that require appropriate
 context or even guessing to understand.  What we're going to do in
 this homework is to use a formal language, ACL2s, as the metalanguage
 and we are going to define and reason about an arithmetic expression
 language that includes errors.

 We are also going to use a gradual verification methodology supported
 by ACL2s. This is ongoing, early stage work that allows us to design
 systems that get verified gradually. 

 One final note. We will see how to use ACL2s as both the metalanguage
 and the object language, in the extra credit problems, which I
 encourage you to do. 

|#

(in-package "ACL2S")

;; First, update ACL2s, by running the script clean-gen-acl2-acl2s.sh

#|
  
 Here is a short overview of gradual verification. ACL2s supports the
 design, development and verification of computational systems by
 allowing you to set certain parameters. There are four built-in
 configurations we are going to consider. In order of most to least
 permissive, they are:
 
 (modeling-start): This is the configuration you will start with. In
 this configuration, ACL2s will accept anything you tell it, unless it
 can very quickly find a counterexample. ACL2s will not prove
 termination, nor will it prove function and body contracts nor will
 it prove named properties (defthms).
 
 (modeling-validate-defs): In this configuration, ACL2s will now try
 proving termination and function/ body contracts, but if it can't it
 will accept your definitions anyway. It will also give itself a bit
 more time for testing.
 
 (modeling-admit-defs): In this configuration, ACL2s will require
 proofs of termination and function/body contracts. It will also give
 itself more time for testing.
 
 (modeling-admit-all): In this configuration, ACL2s will require
 proofs of properties. You can enable/disable proofs locally. More on
 that below.

 Remember that ACL2s is going to be doing a lot of theorem proving and
 counterexample generation when admitting definitions and checking
 properties. When using the gradual verification methodology, you get
 some default settings that control how much time ACL2s spends on
 various tasks and you will find yourself in a situation where you
 want to adjust those settings. Here is a summary of some of the more
 common ways in which you may want to adjust what ACL2s does. There
 are global and local settings.

 Global settings:

 1. To turn testing/counterexample generation on/off (t/nil):
    (acl2s-defaults :set testing-enabled t/nil) ; use t or nil not t/nil

 2. To skip function admissibility proofs (testing can still find
    problems for any of the skip forms):
    (set-defunc-skip-admissibilityp t/nil)

 3. To skip function contract proofs:
    (set-defunc-skip-function-contractp t/nil)

 4. To skip body contract proofs:
    (set-defunc-skip-body-contractsp t/nil)

 5. To set strictness of termination. For all strict forms: If
    strictness is t, then termination (or whatever) is required. If
    strictness is nil, ACL2s will try proving it, but if it can't it
    will assume that it holds.
    (set-defunc-termination-strictp t/nil)

 6. To set set strictness of function contract proofs.
    (set-defunc-function-contract-strictp t/nil)

 7. To set set strictness of body contract proofs.
    (set-defunc-body-contracts-strictp t/nil)

 8. Do properties need to be proved to be accepted?
    (set-acl2s-property-table-proofs? t/nil)

 9. Should properties be tested?
    (set-acl2s-property-table-testing? t)
 
 10. Set timeouts for:  
       cgen: total time counterexample generation gets
       cgen-local: time cgen gets for individual subgoals.
       defunc: time defunc/definec get
       table: time for property testing/ proving

     (modeling-set-parms cgen cgen-local defunc table)

 Local settings: You can add keyword arguments to specific
 properties. For example

 (property (x :tl)
   :proof-timeout 10
   :proofs? t
   (== x x))

 1. Timeout after n seconds when doing a proof
    :proof-timeout n

 2. Timeout after n seconds when testings.
    :testing? n
             
 3. Whether to require proofs
    :proofs? t/nil

 4. Whether to require testing
    :testing? t/nil

|#

; Start with this configuration and once you are done with the
; homework, go to the next configuration, cranking up the rigor as far
; as you can. You must get to at least (modeling-validate-defs), but
; (modeling-admit-defs) is better and (modeling-admit-all) is the
; best.

(modeling-admit-all)

#|

 We will define the syntax and semantics for SAEL, the Simple
 Arithmetic Expression Language. So, SAEL is our object language. The
 metalanguage we (you) will use to define SAEL is ACL2s. The
 meta-metalanguage we (I, in this assignment) use to discuss all of
 this is Mathematical English.

 A simple arithmetic expression, saexpr, is one of the following:

 - a rational number (we use the builtin ACL2s type rational)

 - a variable (we use the builtin ACL2s type var)

 - a list of the form 
   
   (- <saexpr>)
   (/ <saexpr>)

   where <saexpr> is an arithmetic expression

 - a list of the form

   (<saexpr> <oper> <saexpr>)

   where <oper> is one of +, -, *, / or ^ 
   and both <saexpr>'s are simple arithmetic expressions.

|#

; It really isn't important to know the exact definition of varp,
; although you can query ACL2s with ":pe varp". Just notice that none
; of the operators are vars, but symbols such as x, y, z, etc are
; vars.

(check= (varp '-) nil)
(check= (varp '+) nil)
(check= (varp '*) nil)
(check= (varp '/) nil)
(check= (varp '^) nil)
(check= (varp 'x) t)

;; Use defdata to define the unary operators. Fill in the ...s
;; below. If you have questions, ask on Piazza.
(defdata uoper (enum '(- /)))

;; Use defdata to define boper the binary operators

(defdata boper (enum '(+ - * / ^)))

(check= (boperp '*) t)
(check= (boperp '^) t)
(check= (boperp '!) nil)

;; Use defdata to define saexpr. We will want names for all the
;; subtypes, so use the following template. Note that data definitions
;; can be mutually recursive.

(defdata
  (saexpr (or rational  ; or is the same as oneof
              var
              usaexpr   ; unary sael expression
              bsaexpr)) ; binary sael expression
  (usaexpr (list uoper saexpr))
  (bsaexpr (list saexpr boper saexpr)))

;; We now have a formal definition of the SAEL language!  That is, we
;; have a recognizer saexprp, which is defined in our metalanguage,
;; ACL2s, and which recognizes expression in the object language,
;; SAEL. We formalized the syntax of SAEL expressions.

(check= (saexprp '((x + y) - (/ z))) t)
(check= (saexprp '(x + y + z)) nil)

;; We are now going to define the semantics of SAEL expressions.

;; First, some helper definitions.
;; An assignment is an alist from var's to rationals.
;; An alist is just a list of conses.
;; In my RAP notes and in the Harrison book, the term "valuation" is
;; also used instead of assignment.

(defdata assignment (alistof var rational))

(check= (assignmentp '((x . 1) (y . 1/2))) t)

;; This is nil because (1), (1/2) are not rationals.
(check= (assignmentp '((x 1) (y 1/2))) nil)

;; Now, on to the semantics.

;; How do we assign semantics to SAEL expressions such as
;; (x + y)? 

;; We will define saeval (below), a function that given an saexpr and
;; an assignment evaluates the expression, using the assignment to
;; assign values to var's.

;; If a var appears in the saexpr but not in the assignment, then
;; the value of the var should be 1.

;; Use the following helper function to lookup the value of v in a
;; (remember return 1 if v isn't in a)

(definec lookup (v :var a :assignment) :rational
  (let ((res (assoc v a)))
    (if res (cdr res) 1)))

;; What happens when we divide by 0? We are going to throw an
;; error. So, we will model that as follows.

;; A singleton type
(defdata er 'error)

;; *er* is defined using the enumerator for er, which always retuns
;; 'error; if we change er, we will not have to change *er*. Instead
;; of using the symbol 'error, use the constant *er* in the code you
;; write. 
(defconst *er* (nth-er-builtin 0))

;; Since the evaluation of arithmetic expressions can yield errors, we
;; will define the type that evaluation can return to include errors.
(defdata rat-err (or rational er))

;; There are some decisions to be made.

;; First: if an error occurs during evaluation, then you must return
;; the error; there is no mechanism for masking errors.

;; Second: If you divide by 0, that is an error.

;; Third: How do we define exponentiation? For example, do we allow
;; (-1 ^ 1/2) or (2 ^ 1/2) or (0 ^ -1)? All three are problematic, for
;; different reasons. In the first case, the result is i, but we only
;; allow rationals, not complex numbers. In the second case, we get an
;; irrational. In the third case, ^ is undefined, as it would require
;; us to divide by 0.

;; To stay in the realm of rationals, given an expression of the form
;; (x ^ y), we return an error if (1) y is not an integer or (2) x=0
;; and y<0.

;; By the way, the builtin exponentiation function in ACL2s is expt.

;; Feel free to define helper functions as needed.

(definec saeval-uoper (op :uoper v :rat-err) :rat-err
  (match v
    (:er *er*)
    (& (match op
         ('- (- v))
         ('/ (if (= v 0) *er* (/ v)))))))

(definec saeval-boper (op :boper x :rat-err y :rat-err) :rat-err
  (if (or (erp x) (erp y))
      *er*
      (match op
        ('+ (+ x y))
        ('- (- x y))
        ('* (* x y))
        ('/ (if (= y 0) *er* (/ x y)))
        ('^ (if (or (not (integerp y)) (and (= x 0) (< y 0)))
                *er*
                (expt x y))))))

(definec saeval (e :saexpr a :assignment) :rat-err
  (match e
    (:rational e)
    (:var (lookup e a))
    (:usaexpr
      ((op x) (if (and (uoperp op) (saexprp x))
		  (saeval-uoper op (saeval x a))
		  *er*))
      (& *er*))
    (:bsaexpr
      ((x op y) (if (and (boperp op) (saexprp x) (saexprp y))
		    (saeval-boper op (saeval x a) (saeval y a))
		    *er*))
      (& *er*))))

(check= (saeval '((x + y) - (- z))
                '((y . 3/2) (z . 1/2)))
        3)

;; Now, we can state and prove properties about the object language,
;; e.g., splecify the property:

;; 0. For (SAEL) variable x, x=x

;; Here is the answer.

(property (a :assignment)
  (== (saeval 'x a)
      (saeval 'x a)))

;; In the above statement, I used Mathematical English (our
;; meta-metalanguage) to request that you specify a property
;; (x=x). What I am asking you to do is to use ACL2s, the
;; metalanguage, to state a property of SAEL, the object language.
;; Notice that x=x means that x=x always, which means for every
;; possible assignment, the evaluation of x = the evaluation of x.
;; Also notice that x is a specific SAEL variable; it is not an ACL2s
;; variable ranging over SAEL variables. How would you write that?

;; I will stop being so pedantic about what is going on in the
;; following exercises.

;; Next topic. Notice the property form, above.  It is similar to
;; definec in that you identify the variables and their types first
;; and then you have the body of the property. How ACL2s handles
;; properties depends on the configuration, so as you crank up the
;; rigor, ACL2s will demand more. You can override configuration
;; parametrs. Here is an silly example showing some of the parameters.

(property (a :assignment)
  :testing? t
  :testing-timeout 20
  :proofs? t
  :proof-timeout 1
  (== (saeval 'x a)
      (saeval 'x a)))

;; What if I had instead asked you to specify
;; 0. For all (SAEL) variables x, x=x
;; As discussed above this is different than what I originally
;; asked. Make sure you understand why.

;; Here is the answer.

(property (x :var a :assignment)
  (== (saeval x a)
      (saeval x a)))

;; Notice that I can instantiate the above property to get y=y, for
;; SAEL variable y, but I can't do that with the original property.
;; The above form will show cases in which the conjecture is
;; true. Look at those cases to see that ACL2s tests the above
;; property with different object variables substituted for x.

;; Specify the following properties about SAEL. Are they valid? If
;; not, make them valid in the least restrictive way. Feel free to
;; define helper functions, if that helps.

;; 1. -x = -(-(-x)), for var x

(property (a :assignment)
  (== (saeval '(- x) a)
      (saeval '(- (- (- x))) a)))

;; 2. (x - y) = (x + (- y)), for *any* vars x, y
;; Hint: the backquote/comma combo can be your friend.

(property (x :var y :var a :assignment)
  (== (saeval `(,x - ,y) a)
      (saeval `(,x + (- ,y)) a)))

;; 3. (x * (y + z)) = ((x * y) + (x * z)), for saexpr's x, y, z
;; Note! x, y, z are saexpr's not vars!

(property (x :saexpr y :saexpr z :saexpr a :assignment)
  (== (saeval `(,x * (,y + ,z)) a)
      (saeval `((,x * ,y) + (,x * ,z)) a)))

;; Notice that the following is true because error = error.

(check= (saeval '(/ 0) nil)
        (saeval '(1 / 0) nil))

;; 4. (1 / (x / y)) = (y / x), for saexpr's x, y,

(property (x :saexpr y :saexpr a :assignment)
  :hyps (let ((xval (saeval x a))
	      (yval (saeval y a)))
	  (and (rationalp xval)
	       (rationalp yval)
	       (not (== xval 0))
	       (not (== yval 0))))
  (== (saeval `(1 / (,x / ,y)) a)
      (saeval `(,y / ,x) a)))

;; 5. (0 ^ x) = 0, for saexpr x

(property (x :saexpr a :assignment)
  :hyps (and (integerp (saeval x a))
             (> (saeval x a) 0))
  (== (saeval `(0 ^ ,x) a)
      0))

;; 6. (x ^ ((2 * y) / y)) = (x ^ 2), for saexpr's x, y

(property (x :saexpr y :saexpr a :assignment)
  :hyps (and (not (== (saeval y a) 0))
             (rationalp (saeval y a)))
  (== (saeval `(,x ^ ((2 * ,y) / ,y)) a)
      (saeval `(,x ^ 2) a)))

;; This part is intentially vague in places. That's an opportunity for
;; you to learn. If there is confusion, ask!

;; Define the notion of an ACL2s arithmetic expression over rationals
;; that has the same operators as SAEL, but uses ACL2s prefix syntax
;; and ACL2s function names; the only name you have to change is ^ to
;; expt.  Use defdata and call such expressions aaexpr's. Feel free to
;; use previous data definitions.

(defdata aoper (enum '(+ - * / expt)))

(defdata
  (aaexpr (or rational
              var
              uaaexpr
              baaexpr))
  (uaaexpr (list uoper aaexpr))
  (baaexpr (list aoper aaexpr aaexpr)))

;; Define functions sael->aa and aa->sael that transform SAEL
;; and ACL2s arithmetic expressions to each other.

(definec sael->aa (e :saexpr) :aaexpr
  (match e
    (:rational e)
    (:var e)
    (:usaexpr
      (('- x) (list '- (sael->aa x)))
      (('/ x) (list '/ (sael->aa x))))
    (:bsaexpr
      ((x '+ y) (list '+ (sael->aa x) (sael->aa y)))
      ((x '- y) (list '- (sael->aa x) (sael->aa y)))
      ((x '* y) (list '* (sael->aa x) (sael->aa y)))
      ((x '/ y) (list '/ (sael->aa x) (sael->aa y)))
      ((x '^ y) (list 'expt (sael->aa x) (sael->aa y))))))

(definec aa->sael (e :aaexpr) :saexpr
  (match e
    (:rational e)
    (:var e)
    (:uaaexpr
      (('- x) (list '- (aa->sael x)))
      (('/ x) (list '/ (aa->sael x))))
    (:baaexpr
      (('+ x y) (list (aa->sael x) '+ (aa->sael y)))
      (('- x y) (list (aa->sael x) '- (aa->sael y)))
      (('* x y) (list (aa->sael x) '* (aa->sael y)))
      (('/ x y) (list (aa->sael x) '/ (aa->sael y)))
      (('expt x y) (list (aa->sael x) '^ (aa->sael y))))))

;; State the two properties that the above functions are inverses of
;; each other.

(property (e :saexpr)
  (== (aa->sael (sael->aa e))
      e))

(property (e :aaexpr)
  (== (sael->aa (aa->sael e))
      e))

;; Define an evaluator, aaeval, for ACL2s arithmetic expressions
;; (similar to saeval). What is interesting here is that I am using
;; the metalanguage to study itself, i.e., I am defining the syntax
;; and semantics of ACL2s in ACL2s. 

;; In the definition of aaeval, if there is a divide by 0, aaeval will
;; return 0. For (expt x y) where y=0 or not an integer, aaeval will
;; return 1; otherwise, if x=0, aaeval will return 0. So aaeval always
;; returns a rational. Now, this may not seem like ACL2s, but it
;; actually is what ACL2s does in the "core" logic, which you can
;; experiment with by issuing the command (set-guard-checking nil). 

(definec aaeval-uoper (op :uoper v :rational) :rational
  (match op
    ('- (- v))
    ('/ (if (= v 0) 0 (/ v)))))

(definec aaeval-aoper (op :aoper x :rational y :rational) :rational
  (match op
    ('+ (+ x y))
    ('- (- x y))
    ('* (* x y))
    ('/ (if (= y 0) 0 (/ x y)))
    ('expt (if (or (not (integerp y)) (= y 0))
            1
            (if (= x 0)
                0
                (expt x y))))))

(definec aaeval (e :aaexpr a :assignment) :rational
  (match e
    (:rational e)
    (:var (lookup e a))
    (:uaaexpr
      ((op x) (if (and (uoperp op) (aaexprp x))
		  (aaeval-uoper op (aaeval x a))
		  *er*))
      (& *er*))
    (:baaexpr
      ((op x y) (if (and (aoperp op) (aaexprp x) (aaexprp y))
		    (aaeval-aoper op (aaeval x a) (aaeval y a))
		    *er*))
      (& *er*))))

;; State properites relating aaeval to saeval. Make them as general as
;; possible. Start with if I have an SAEL expression and I convert it
;; to an ACL2s arithmetic expression, then for any assignment, the
;; corresponding evaluations agree. And the other way around (start
;; with ACL2s arithmetic expression). These two properties are
;; enough. Notice that this allows us to use the metalanguage to prove
;; theorems establishing a correspondence between object language
;; theorems and metalanguage theorems.

(property (e :saexpr a :assignment)
  :hyps (not (erp (saeval e a)))
  (== (saeval e a)
      (aaeval (sael->aa e) a)))

(property (e :aaexpr a :assignment)
  :hyps (not (erp (saeval (aa->sael e) a)))
  (== (aaeval e a)
      (saeval (aa->sael e) a)))

;; Extra credit 2 (25 points, all or nothing)

;; Do this in another theorem prover of your choice. Try to make it as
;; equivalent as possible and try to prove the same theorems, write
;; the same tests and properties. Provide a summary of your findings.
;; This is only recommended for those of you that already have
;; experience with other theorem provers. Examples of other theorem
;; provers include lean, acl2, coq, pvs, agda, isabelle, hol (and
;; variants), etc.

