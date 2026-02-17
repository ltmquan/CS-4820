#|

Author: Pete Manolios
Date:   1/23/2026

Code used in lecture 5 of Computer-Aided Reasoning.

|#

(in-package "ACL2S")

"START Automated Rev-Rev Demo
"

(set-gag-mode nil)

(definec ap (a b :tl) :tl
  (if (endp a)
      b
    (cons (car a) 
          (ap (cdr a) b))))

:u

(definec ap (a b :tl) :tl
  (match a
    (nil b)
    ((f . r) (cons f (ap r b)))))

(check= (ap '(1 2 3) '(4 5 6))
        '(1 2 3 4 5 6))

(definec rv (x :tl) :tl
  (if (endp x)
      nil
    (ap (rv (cdr x))
        (list (car x)))))

:u

(definec rv (x :tl) :tl
  (match x
    (nil nil)
    ((f . r) (ap (rv r) (list f)))))

(check= (rv '(1 2 3)) '(3 2 1))

"Show  ld

(ld \"l6.lisp\")
"

"This is a classic example that shows ACL2 going through all of the
 proof procedures.
"

(property rv-rv (x :all)
  (== (rv (rv x))
      x))

"Contract completion
"

(property rv-rv (x :tl)
  (== (rv (rv x))
      x))

"END Automated Rev-Rev Demo
"

"It is a good idea to not allow ACL2s to do nested inductions. There
 are several reasons for this.

 1. The theorems needed to avoid nested induction proofs are typically
 useful theorems to have around. You just discovered these interesting
 theorems, so by turning them into defthms, named properties, the
 theorem prover will be able to use them in subsequent proofs.

 2. It makes your proofs more robust. This is a big deal for proof
 engineering, where you don't have simple changes to your definitions/
 properties to require lots of proof re-engineering.

 First, we undo the previous theorem.
"

:u

"Next, we set the induction-depth-limit to 1, which means ACL2s can do
 proofs by induction, but cannot do nested inductions.
"

(set-induction-depth-limit 1)

"Do the proof 
"

(property lem1 (x y :tl)
  (== (rv (ap x y))
      (ap (rv y) (rv x))))

(property lem2 (x y z :tl)
  (== (ap (ap x y) z)
      (ap x (ap y z))))

(property ap-associative (x y z :tl)
  (== (ap (ap x y) z)
      (ap x (ap y z))))

(property (x y :tl)
  (== (rv (ap x y))
      (ap (rv y) (rv x))))

(property lem3 (x :tl)
  (== (ap x nil)
      x))

(property ap-nil (x :tl)
  (== (ap x nil)
      x))

(property ap-rv (x y :tl)
  (== (rv (ap x y))
      (ap (rv y) (rv x))))

(property rv-rv (x :tl)
  (== (rv (rv x))
         x))

:u

"How to tell ACL2s what induction scheme to use. Notice that the
 proof obligations are different than before.
"

(property rv-rv (x :tl)
  (== (rv (rv x))
      x)
  :hints (("goal" :induct (tlp x))))

"ACL2s uses previous theorems in subsequent proof attempts.
"

(property (x :tl)
  (== (rv (rv (rv x)))
      (rv x)))

(property (x y :tl)
  (== (ap (rv (rv (rv x))) (ap x (ap y nil)))
      (ap (rv x) (ap x y))))
