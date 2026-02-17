(in-package "ACL2S")
(set-gag-mode nil)

(modeling-admit-all)
(set-termination-method :measure)
(set-induction-depth-limit 1)

"Measure function m-bad-app"
(definec m-bad-app (x y :tl acc :all) :nat
  (cond ((^ (endp x) (endp y)) 0)
         ((endp x) (len y))
         ((endp y) (1+ (len x)))
         (t (+ 2 (len acc) (len x)))))

"Main function bad-app"
(definec bad-app (x y acc :tl) :tl
  (declare (xargs :measure (m-bad-app x y acc)))
  (match (list x y)
    ((nil nil) acc)
    ((& nil) (bad-app y x acc))
    ((nil (f . r)) (bad-app x r (cons f acc)))
    (& (bad-app x nil (bad-app acc nil y)))))

"Relationship between bad-app and app (should fail)"
(property bad-app-n-app (x y acc :tl)
  (== (bad-app x y acc)
      (if (endp x)
          (app (rev y) acc)
          (if (endp y)
              (app (rev x) acc)
              (app (rev x) (rev acc) y)))))

"I tried to prove a subcase for it first, using two additional lemmas."
(property bad-app-lemma1 (e :all x y :tl)
  (== (bad-app nil (cons e x) y)
      (bad-app nil x (cons e y))))

(property bad-app-lemma2 (e :all x y :tl)
  (== (app (append x (list e)) y)
      (app x (cons e y))))

(property bad-app-x-nil (y acc :tl)
  (== (bad-app nil y acc)
      (app (rev y) acc))
  :hints (("goal" :induct (tlp y))))

"The subcase fails, but tracing where it failed, I noticed it got stuck here:
(implies (and (tlp rv)
              (cons y1 y2)
              (equal (bad-app nil y2 acc)
                     (app rv acc))
              (tlp y2)
              (tlp acc))
         (equal (bad-app nil y2 (cons y1 acc))
                (app rv (cons y1 acc)))).
Why doesn't ACL2s simply apply the induction hypothesis here?"
