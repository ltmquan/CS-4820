#|

Author: Pete Manolios
Date:   1/30/2026

Code used in lecture 7 of Computer-Aided Reasoning.  

Topics:

  Macros 
  Books
  State/World
  Performance issues: accumulated persistence
  Libraries

|#

(in-package "ACL2S")
(set-gag-mode nil)


"
Let's look at some examples of macros. Here is an example when
we discussed defdata. Defdata is a macro, so let's see what it
translates into."

:trans1
(defdata file (list string nat))

"
Notice the with-output form.

It allows us to control how much output a user sees.

So, if something fails, or if we want to explore, we can strip that
out.

Next, let's look at the defdata::defdata-events form.
"

(defdata::defdata-events
  (defdata::parse-defdata '(file (list string nat))
    (current-package state)
    (w state))
  (w state))

"
First, notice state and (w state), the world.

The ACL2 logical world is a data structure that includes all logical
content resulting from the commands evaluated.  The world includes a
representation of the current logical theory, as well as some
extra-logical information such as the values of ACL2 tables.

Let's look at the documentation on state.
"

"
Back to the defdata.
Again, we can pull out the with-output body, which is a progn and we
can submit each argument to the progn to ACL2 to see what happens.  We
won't do that, but notice the definitions of the recognizer, the
enumerator and a version of the enumerator that takes a seed:

  (defun filep (d1) ...)
  (defun nth-file-builtin (i1) ...)
  (defun nth-file/acc-builtin (size1 defdata::_seed) ...)

Let's submit this.
"

(defdata file (list string nat))

"
Now, the more interesting form.
"

:trans1
(defdata 
  (dir (list string dir-file-list))
  (dir-file-list (listof file-dir))
  (file-dir (or file dir)))

"
As before, let's look at the defdata::defdata-events form.
"

(defdata::defdata-events
  (defdata::parse-defdata '((dir (list string dir-file-list))
                            (dir-file-list (listof file-dir))
                            (file-dir (or file dir)))
    (current-package state)
    (w state))
  (w state))


"
I bring your attention to the following form that shows how to
define mutually recursive functions. I remove package names
to make this more readable.

(mutual-recursion
 (defun dirp (d1)
   (declare (xargs :guard t))
   (and (consp d1)
        (stringp (car d1))
        (and (consp (cdr d1))
             (dir-file-listp (car (cdr d1)))
             (equal (cdr (cdr d1)) nil))))
 (defun dir-file-listp (d1)
   (declare (xargs :guard t))
   (or (equal d1 nil)
       (and (consp d1)
            (file-dirp (car d1))
            (dir-file-listp (cdr d1)))))
 (defun file-dirp (d1)
   (declare (xargs :guard t))
   (or (filep d1) (dirp d1))))

Notice that we need to prove termination to show that this
defdata makes sense.
"

"
Let's submit it.
"

(defdata 
  (dir (list string dir-file-list))
  (dir-file-list (listof file-dir))
  (file-dir (or file dir)))

"
Can you write defdatas that don't make sense?

Sure. Here is an example that differs from the above by a few
characters.
"

:u

(defdata 
  (dir (list string dir-file-list))
  (dir-file-list (listof file-dir))
  (file-dir (or file file-dir)))

"
Here is simpler example.
"

(defdata 
  (foo (or string bar))
  (bar (or nat foo)))


"
Let's discuss libraries and books.
"

:pbt -7

"
Let's look at some of the books that are included.

Let's start with base-theory.
"

"
Next, let's look at std/lists/top.
"

"
Notice that there are lots of libraries (books) that are used to
reason about true-lists, app, len, rev, etc. So, example, we can
see what rules are available for reasoning about true-listp, as
follows.
"

:pl append
:doc pl
:pl tlp
:pl (rev (app x y))
:pf (:type-prescription rev)

"
Especially with all of these theorems pre-loaded,
you may want to figure out why something is taking so long.
A really useful utility is accumulated-persistence.
"

:doc accumulated-persistence


"
We have seen that app is a macro that allows multiple arguments.
For example.
"

(app '(1 2) '(3 4) '(5 6))
(app)

"
Let's see how app is defined.
"

:pe app

"
So notice what is reported. That app is a macro alias for 
the function bin-app. This allow us/ACL2 to use/display 
app instead of bin-app in certain contexts. For
example: notice the output below refers to app
"

(property (x y :tl)
  :hyps (or (null x) (null y))
  :body (== (bin-app x y)
            (bin-app y x)))

"
You have to be somewhat careful because app is a macro that
expands into bin-app.
"

:pe app

:trans1 (app x y)

"
And, bin-app is a non-recursive definition, so 
the theorem prover will use rewriting to expand it
into its body.

   (app x y)
-> { macro expansion }
   (bin-app x y)
-> { rewriting }
   (append x y)
-> { macro expansion }
   (binary-append x y)
"

:trans1 (append x y)

"
The way I defined app is good, for several reasons:

1. It allows me to use the previous definition of 
   append, but with different contracts.

So, I really want app and append to be different. 
"

(property (x :tl y :all)
  (== (append x y)
      (append x y)))

(property (x :tl y :all)
  (== (app x y)
      (app x y)))

"
2. I can use all the previous theorems for append, for free.
   How? By just expanding app into append.

But, there is a price.

I have to be aware that the rewriter will do what I told
it and my rewrite strategy is to turn app into append.

So, if I write rewrite rules where the pattern is 

(app ...)

That's a bad idea and I should instead use the pattern

(append ...)

So, if you prove a theorem of the form
(=> ... (== (app x y) ...))

this will probably never match.

Instead, you should prove
(=> ... (== (append x y) ...))

Using macros in rewrite rules is fine, as they get expanded
away, i.e., the above is equivalent to

(=> ... (== (binary-append x y) ...))
"

"
Let's define our own append as follows.
"

(definec binary-ap (x y :tl) :tl
  (match x
    (() y)
    ((f . r) (cons f (binary-ap r y)))))

"
It would be nice to have a macro, say ap, that can take
an arbitrary number of arguments.

This is syntactic sugar that is easy to add with lisp-based
languages, but hard to do in most languages. 

There is a utility ACL2s provides for doing this.
"

:doc make-n-ary-macro

:trans1 (make-n-ary-macro ap binary-ap nil t)

(make-n-ary-macro ap binary-ap nil t)

"
So, make-n-ary-macro defines the macro ap and adds it to the
macro-aliases-table. Let's look at the documentation.
"

:doc acl2::macro-aliases-table
:doc acl2::add-macro-fn

"
SUGGESTION:
Download a local copy of the ACL2 manual and you can use your browser
to search the documentation.
"

"
And now we try proving the same thm as before,
notice the output below refers to ap, not binary-ap "

(property (x :tl)
  (== (ap x nil) x)
  :hints (("goal" :induct (tlp x))))

(property (x y :tl)
  :hyps (or (null x) (null y))
  :body (== (ap x y)
            (ap y x)))

"
In ACL2s, tlp is a macro alias for true-listp and so on."


"
Notice that such macros are also supported in the proof builder.
The proof builder is a low-level theorem prover where you can
complete control what ACL2 does. It can be useful for understanding
what is going on in a failed proof.

You have to write conjecture in expanded form as shown below.
"

(verify
 (=> (and (tlp x) (tlp y)
          (or (null x) (null y)))
     (equal (ap x y)
            (ap y x))))
th
(help th)
pro
(help pro)
(help split)
th
split
th
cg
th
bash
th
pp
(help pp)
p
(help p)
bash
prove
(help exit)
(exit t)

"
Let's say that we want to prove the conjecture using the proof
builder. We can use the powerful prove command.
"

(verify
 (implies (and (tlp x) (tlp y) (or (null x) (null y)))
          (equal (ap x y)
                 (ap y x)))
 :instructions (prove))

(help prove)
exit

"
Let's say that we want to have more control since prove can
generalize. We just want to use induction and simplification.
"

(verify
 (implies (and (tlp x) (tlp y) (or (null x) (null y)))
          (equal (ap x y)
                 (ap y x)))
 :instructions ((do-all induct bash)))

(help induct)
(help bash)
goals
th
pro
th
bash
goals
th
exit

"
Since induction generated multiple subgoals, we may want to apply
bash to all of them.
"

(verify
 (implies (and (tlp x) (tlp y) (or (null x) (null y)))
          (equal (ap x y)
                 (ap y x)))
 :instructions ((do-all induct (repeat bash))))

(help repeat)
goals
th
exit

"
But we still have another goal and that requires induction.
So, let's repeat once more.
"

(verify
 (implies (and (tlp x) (tlp y)
               (or (null x) (null y)))
          (equal (ap x y)
                 (ap y x)))
 :instructions ((repeat
                 (do-all induct
                         (repeat bash)))))

exit

"
Oops. Infinite loop.

It would be nice to have an instruction that allows us to repeatedly
apply instructions until all goals have been proved.

Here is how we can do that. We essentially define a macro, which
is a new tactic.

Macros are described in the reading material, CAR, but let's
use :doc to remind ourselves how to define macros.
"

:doc defmacro

"
There is a lot of information about macros. See the following.
"

:doc acl2::macros

"
There is support for defining proof builder macros. Here is a
documentation topic.
"

:doc define-pc-macro

(define-pc-macro repeat-until-done (&rest instrs)
  (value
   `(repeat (do-all
             ,@(append instrs 
                       `((negate (when-not-proved fail))))))))

"
There is even a mechanism for creating documentation for the ACL2
manual.
"

(defxdoc acl2-pc::repeat-until-done
  :parents (proof-builder-commands)
  :short "(macro)
Repeat the given instructions until all goals have been proved"
  :long "@({
 Example:
 (repeat-until-done induct (repeat bash))

 General Form:
 (repeat-until-done instr1 ... instrk)
 })

 <p>where each @('instri') is a proof-builder instruction.</p>")


"
Now use let's use our new macro.
"

(verify
 (implies (and (tlp x) (tlp y)
               (or (null x) (null y)))
          (equal (ap x y)
                 (ap y x)))
 :instructions ((repeat-until-done induct (repeat bash))))

exit

"
And if we want to generate a dummy defthm whose proof uses
the proof builder, we can do this.
"

(verify
 (implies (and (tlp x) (tlp y) (or (null x) (null y)))
          (equal (ap x y)
                 (ap y x)))
 :instructions ((repeat-until-done induct (repeat bash))
                (exit t)))

"
If we want to generate a defthm/property, named my-thm, with
rule-classes nil, we can do this. 
"

(verify
 (implies (and (tlp x) (tlp y) (or (null x) (null y)))
          (equal (ap x y)
                 (ap y x)))
 :instructions ((repeat-until-done induct (repeat bash))
                (exit my-thm nil)))

y

"
Or
"

:u

(property my-thm (x y :tl)
  :h (or (null x) (null y))
  :b (== (ap x y) (ap y x))
  :instructions ((repeat-until-done induct (repeat bash))
                 (exit my-thm nil)))

"
Using the theorem prover to prove equivalence of
rv (inefficient)
with rv* (efficient)
"

(definec rv (x :tl) :tl
  (match x
    (() ())
    ((f . r) (ap (rv r) `(,f)))))

(definec makelst (n :nat) :tl
  (match n
    (0 ())
    (& (cons n (makelst (1- n))))))

(makelst 10)

(time$ (b* ((l (rv (makelst 10)))) (len l)))
(time$ (b* ((l (rv (makelst (expt 2 12))))) (len l)))
(time$ (b* ((l (rv (makelst (expt 2 13))))) (len l)))
(time$ (b* ((l (rv (makelst (expt 2 14))))) (len l)))
(time$ (b* ((l (rv (makelst (expt 2 15))))) (len l)))

(definec rvt (x acc :tl) :tl
  (match x
    (() acc)
    ((f . r) (rvt r (cons f acc)))))

(definec rv* (x :tl) :tl
  (rvt x nil))

(time$ (b* ((l (rv (makelst (expt 2 14))))) (len l)))
(time$ (b* ((l (rv* (makelst (expt 2 14))))) (len l)))
(time$ (b* ((l (rv* (makelst (expt 2 20))))) (len l)))

"
We want efficient execution (rv*) and simple reasoning (rv).
So, we first prove the following.
"

(property ap-associative (x y z :tl)
  (== (ap (ap x y) z)
      (ap x (ap y z))))

(property rvt-rv (x acc :tl)
  (== (rvt x acc)
      (ap (rv x) acc)))

(property ap-nil (x :tl)
  (== (ap x nil) x))

(property rv*=rv (x :tl)
  (== (rv* x) (rv x)))

"
Add enough lemmas to prove the above property.
Use the method.
"

"
Then we disable rv* and prove theorems about rv:
"
(in-theory (disable rv*-definition-rule))

(property rv-ap (x y :tl)
  (== (rv (ap x y))
      (ap (rv y) (rv x))))

(property rv-rv (x :tl)
  (== (rv (rv x)) x))

; Next thm follows from equivalence between rv* and rv directly.

(property (x :tl)
  (== (rv* (rv* x)) x))

"
Reasoning about sets.
We start with the definition of set equality.
"

(defdata-alias set tl)

(definec s<= (x y :set) :bool
  (match x
    (() t)
    ((f . r) (and (in f y) (s<= r y)))))

(definec s= (x y :set) :bool
  (^ (s<= x y) (s<= y x)))


"
Prove that s= is an equivalence relation
"
(property s-lemma (x y :set a :all)
  :h (s<= x y)
  :b (s<= x (cons a y)))
  
(property s<=-reflexive (x :set)
  (s<= x x))

(property s=-reflexive (x :set)
  (s= x x))

(property s=-symmetric (x y :set)
  :h (s= x y)
  :b (s= y x))

(property s-lemma2 (x y :set a :all)
  :h (^ (s<= x y) (in a x))
  :b (in a y))

(property s<=-transitive (x y z :set)
  :h (^ (s<= x y) (s<= y z))
  :b (s<= x z))

(property s=-transitive (x y z :set)
  :h (^ (s= x y) (s= y z))
  :b (s= x z))

"
Add enough lemmas to prove the following property.
Use the method.
"

(property ll4 (x y :set a :all)
  :h (in a x)
  :b (in a (ap x y)))

(property ll3 (x y z :set)
  :h (s<= x y)
  :b (s<= x (ap y z)))

(property ll1 (x :set)
  (s<= (rv x) x))

(property ll2 (x :set)
  (s<= x (rv x)))

(property (x :set)
  (s= (rv* x) x))

"
Exercise.
Do this for nested sets.
Extra credit.
"
