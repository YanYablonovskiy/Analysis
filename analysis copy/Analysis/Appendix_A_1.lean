import Mathlib.Tactic

/-!
# Analysis I, Appendix A.1

An introduction to mathematical statements.  Showcases some basic tactics and Lean syntax.

-/


-- Example A.1.1. What the textbook calls "statements" are objects of type `Prop` in Lean.  Also, in Lean we tend to assign "junk" values to expressions that might normally be considered undefined, so discussions regarding undefined terms in the textbook should be adjusted accordingly.

#check 2+2=4
#check 2+2=5

/-- Every well-formed statement is either true or false... -/
example (P:Prop) : (P=true) ∨ (P=false) := by simp; tauto

--This uses axiom of choice, not clearly stated. This is not true by default.
--Essentially every Prop type is the Unit type or Empty type.

example (P:Prop) : (P=true) ∨ (P=false) := by simp; exact Classical.em P

/-- .. but not both. -/
example (P:Prop) : ¬ ((P=true) ∧ (P=false)) := by simp

#check false_ne_true

--couldnt get it out of the P = .. for a term proof TODO
example (P:Prop) : ¬ ((P=true) ∧ (P=false)) := fun hpnp ↦ false_ne_true sorry



-- Note: `P=true` and `P=false` simplify to `P` and `¬P` respectively.

/-- To prove that a statement is true, it suffices to show that it is not false, -/
example {P:Prop} (h: P ≠ false) : P = true := by simp; tauto


--also seems hard with just terms:




/-- while to show that a statement is false, it suffices to show that it is not true. -/
example {P:Prop} (h: P ≠ true) : P = false := by simp; tauto

/-- This statement is true, but unlikely to be very useful. -/
example : 2 = 2 := rfl

/-- This statement is also true, but not very efficient. -/
example : 4 ≤ 4 := by norm_num


--doable with terms
example : 4 ≤ 4 := le_refl 4



/- This is an expression, not a statement. -/
#check 2 + 3*5

/- This is a statement, not an expression. -/
#check 2 + 3*5 = 17

#check Prime (30+5)

#check 30+5 ≤ 42-7
#reduce 2 + 3*5

#eval 2 + 3*5

#reduce 30+5 ≤ 42-7 --doesnt return true

#eval 30+5 ≤ 42-7 --returns true

/-- Conjunction -/
example {X Y: Prop} (hX: X) (hY: Y) : X ∧ Y := by
  constructor
  . exact hX
  exact hY

example {X Y: Prop} (hXY: X ∧ Y) : X := by
  exact hXY.1

example {X Y: Prop} (hXY: X ∧ Y) : Y := by
  exact hXY.2

example {X Y: Prop} (hX: ¬ X) : ¬ (X ∧ Y) := by
  contrapose! hX
  exact hX.1

example {X Y: Prop} (hY: ¬ Y) : ¬ (X ∧ Y) := by
  contrapose! hY
  exact hY.2

example : (2+2=4) ∧ (3+3=6) := by
  constructor
  . norm_num
  norm_num

/-- Disjunction -/
example {X Y: Prop} (hX: X) : X ∨ Y := by
  left
  exact hX

example {X Y: Prop} (hY: Y) : X ∨ Y := by
  right
  exact hY

example {X Y: Prop} (hX: ¬ X) (hY: ¬ Y) : ¬ (X ∨ Y) := by
  simp
  constructor
  . exact hX
  exact hY

example : (2+2=4) ∨ (3+3=5) := by
  left
  norm_num

example : ¬ ((2+2=5) ∨ (3+3=5)) := by
  simp

example : (2+2=4) ∨ (3+3=6) := by
  left
  norm_num

example : (2+2=4) ∧ (3+3=6) := by
  constructor
  . norm_num
  norm_num

example : (2+2=4) ∨ (2353 + 5931 = 7284) := by
  left
  norm_num

#check Xor'

/-- Negation -/
example {X:Prop} : (¬ X = true) ↔ (X = false) := by simp

example {X:Prop} : (¬ X = false) ↔ (X = true) := by simp

example : ¬ (2+2=5) := by simp

example : 2+2 ≠ 5 := by simp

example (Jane_black_hair Jane_blue_eyes:Prop) :
  (¬ (Jane_black_hair ∧ Jane_blue_eyes)) ↔ (¬ Jane_black_hair ∨  ¬ Jane_blue_eyes) := by
  simp; tauto

example (x:ℤ) : ¬ (Even x ∧ x ≥ 0) ↔ (Odd x ∨ x < 0) := by
  have : ¬ Odd x ↔ Even x := Int.not_odd_iff_even
  have : ¬ (x ≥ 0) ↔ x < 0 := Int.not_le
  tauto

example (x:ℤ) : ¬ (x ≥ 2 ∧ x ≤ 6) ↔ (x < 2 ∨ x > 6) := by
  have : ¬ (x ≥ 2) ↔ (x < 2) := Int.not_le
  have : ¬ (x ≤ 6) ↔ (x > 6) := Int.not_le
  tauto

example (John_brown_hair John_black_hair:Prop) :
  (¬ (John_brown_hair ∨ John_black_hair)) ↔ (¬ John_brown_hair ∧  ¬ John_black_hair) := by
  simp

example (x:ℝ) : ¬ (x ≥ 1 ∧ x ≤ -1) ↔ (x < 1 ∨ x > -1) := by
  have : ¬ (x ≥ 1) ↔ (x < 1) := not_le
  have : ¬ (x ≤ -1) ↔ (x > -1) := not_le
  tauto

example (x:ℤ) : ¬ (Even x ∨ Odd x) ↔ (¬ Even x ∧ ¬ Odd x) := by
  tauto

example (X:Prop) : ¬ (¬ X) ↔ X := by
  simp

/-- If and only if (iff) -/
example {X Y: Prop} (hXY: X ↔ Y) (hX: X) : Y := by
  rw [hXY] at hX
  exact hX

example {X Y: Prop} (hXY: X ↔ Y) (hY: Y) : X := by
  rw [←hXY] at hY
  exact hY

example {X Y: Prop} (hXY: X ↔ Y) (hX: X) : Y := by
  exact hXY.mp hX

example {X Y: Prop} (hXY: X ↔ Y) (hY: Y) : X := by
  exact hXY.mpr hY

example {X Y: Prop} (hXY: X ↔ Y) : X=Y := by
  simp [hXY]

example (x:ℝ) : x = 3 ↔ 2 * x = 6 := by
  constructor
  . intro h
    linarith
  intro h
  linarith

example : ¬ (∀ x:ℝ, x = 3 ↔ x^2 = 9) := by
  simp
  use -3
  norm_cast

example {X Y: Prop} (hXY: X ↔ Y) (hX: ¬ X) : ¬ Y := by
  by_contra this
  rw [←hXY] at this
  contradiction

example : (2+2=5) ↔ (4+4=10) := by
  simp

example {X Y Z:Prop} (hXY: X ↔ Y) (hXZ: X ↔ Z) : [X,Y,Z].TFAE := by
  tfae_have 1 ↔ 2 := by exact hXY  -- This line is optional
  tfae_have 1 ↔ 3 := by exact hXZ  -- This line is optional
  tfae_finish

/-- Note for the `.out` method that one indexes starting from 0, in contrast to the `tfae_have` tactic. -/
example {X Y Z:Prop} (h: [X,Y,Z].TFAE) : X ↔ Y := by
  exact h.out 0 1

/-- Exercise A.1.1.  Fill in the first `sorry` with something reasonable. -/
example {X Y:Prop} : ¬ ((X ∨ Y) ∧ ¬ (X ∧ Y)) ↔ ¬(X ∨ Y) ∨ (X ∧ Y) := by
 constructor
 · intro h
   push_neg at h
   by_cases hc: X ∨ Y
   · exact Or.inr (h hc)
   · exact Or.inl hc
 · intro h
   push_neg
   cases h
   · expose_names
     intro hc
     exact (h hc).elim
   · intros;assumption


/-- Exercise A.1.2.  Fill in the first `sorry` with something reasonable. -/
example {X Y:Prop} : ¬ (X ↔ Y) ↔ ¬(X → Y) ∨ ¬(Y → X) := by
 constructor
 · intro hnif
   by_contra!
   exact hnif ⟨this.1,this.2⟩
 · intro hor
   apply hor.elim
   · intro hxy hif
     exact hxy hif.mp
   · intro hyx hif
     exact hyx hif.mpr

#check Decidable

#print Decidable




/-- Exercise A.1.3. -/
def Exercise_A_1_3 : Decidable (∀ (X Y: Prop), (X → Y) → (¬X → ¬ Y) → (X ↔ Y)) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`, depending on whether you believe the given statement to be true or false.
  apply isTrue
  intro X Y hxy hyx
  have: (¬X → ¬Y) → (Y → X) := by tauto
  exact ⟨hxy,this hyx⟩

/-- Exercise A.1.4. -/
def Exercise_A_1_4 : Decidable (∀ (X Y: Prop), (X → Y) → (¬Y → ¬ X) → (X ↔ Y)) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse
  intro h
  specialize h false true
  tauto






/-- Exercise A.1.5. -/
def Exercise_A_1_5 : Decidable (∀ (X Y Z: Prop), (X ↔ Y) → (Y ↔ Z) → [X,Y,Z].TFAE) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  intro X Y Z hXiY hYiZ
  simp [hXiY,hYiZ]




/-- Exercise A.1.6. -/
def Exercise_A_1_6 : Decidable (∀ (X Y Z: Prop), (X → Y) → (Y → Z) → (Z → X) → [X,Y,Z].TFAE) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry
