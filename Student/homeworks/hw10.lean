/-!
Reminder: You're to read and understand (or send questions) about the material through the currently posted Lecture 20.

Homework: Due Tuesday before class: Formalize the following logical arguments.

Hint: use the variable command to introduce assumed types and such, as we did in class.
Use #check to express the informal propositions that follow in the formal logic of Lean.

1. Every dog likes some cat.

2. If any dog, d, likes any dog, g, and that dog, g, likes any dog, w, then d likes w.

3. If any cat, c, likes any cat, d, then d also likes c.

4. Every cat, c, likes itself.

5. If every cat likes every other cat, and c and d are cats, then c likes d.

Finally, give a formal proof in Lean of the proposition in problem #5.

Put your answers in a new file called hw10.lean. That's what to submit.


As you work through this easy homework, you'll notice that we use the English work, Likes, in several
different ways: to relate cats and dogs, cats and cats, etc. You'll find that you need to use different
identifiers in your formal definitions. For example, I used Likes1, Likes2, and Likes3, just to make the
names different, so that the types will work. --KS
-/


/-!
1. Every dog likes some cat.
-/
namespace prob1
variable
  (Dog : Type)
  (Cat : Type)
  (Likes : Dog → Cat → Prop)

#check ∀ (d : Dog), ∃ (c : Cat), Likes d c
end prob1


/-!
2. If any dog, d, likes any dog, g, and that dog, g, likes any dog, w, then d likes w.
-/
namespace prob2
variable
  (Dog : Type)
  (Likes : Dog → Dog → Prop)

#check ∀ (d : Dog), ∀ (g : Dog), ∀ (w : Dog), Likes d g ∧ Likes g w → Likes d w
#check ∀ (d g w : Dog), Likes d g ∧ Likes g w → Likes d w  -- More concise alternative
end prob2


/-!
3. If any cat, c, likes any cat, d, then d also likes c.
-/
namespace prob3
variable
  (Cat : Type)
  (Likes : Cat → Cat → Prop)

#check ∀ (c d : Cat), Likes c d → Likes d c
end prob3


/-!
4. Every cat, c, likes itself.
-/
namespace prob4
variable
  (Cat : Type)
  (Likes : Cat → Cat → Prop)

#check ∀ (c : Cat), Likes c c
end prob4


/-!
5. If every cat likes every other cat, and c and d are cats, then c likes d.
-/
namespace prob5
variable
  (Cat : Type)
  (Likes : Cat → Cat → Prop)

-- Two ways to write without declaring c and d beforehand
#check (∀ (a b : Cat), Likes a b) → ∀ (c d : Cat), Likes c d
#check ∀ (c d : Cat), (∀ (a b : Cat), Likes a b) → Likes c d

-- Can also declare c and d beforehand
variable
  (c d : Cat)
#check (∀ (a b : Cat), Likes a b) → Likes c d

-- Proof (Using Variables Defined Within the Statement)
example : (∀ (a b : Cat), Likes a b) →
          (∀ (c d : Cat), Likes c d)
| ⟨_, aLikesB⟩ => _

end prob5
