/-
1) Prove the following identities.
-/

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  iff.intro
    (assume h : p ∧ q, ⟨h.right, h.left⟩)
    (assume h : q ∧ p, ⟨h.right, h.left⟩)
example : p ∨ q ↔ q ∨ p := 
  iff.intro
    (assume h : p ∨ q,
      or.elim h
        (assume hp : p, or.inr hp)
        (assume hq : q, or.inl hq))
    (assume h : q ∨ p,
      or.elim h
        (assume hq : q, or.inr hq)
        (assume hp : p, or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  iff.intro
    (assume h : (p ∧ q) ∧ r, ⟨h.left.left, h.left.right, h.right⟩)
    (assume h : p ∧ (q ∧ r), ⟨⟨h.left, h.right.left⟩, h.right.right⟩)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  iff.intro
    (assume h : (p ∨ q) ∨ r,
      or.elim h
        (assume hpq,
          or.elim hpq
            (assume hp : p, or.inl hp)
            (assume hq : q, or.inr (or.inl hq)))
        (assume hr : r, or.inr (or.inr hr)))
    (assume h : p ∨ (q ∨ r),
      or.elim h
        (assume hp : p, or.inl (or.inl hp))
        (assume hqr,
          or.elim hqr
            (assume hq : q, or.inl (or.inr hq))
            (assume hr : r, or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  iff.intro
    (assume h : p ∧ (q ∨ r),
      or.elim h.right
        (assume hq, or.inl ⟨h.left, hq⟩)
        (assume hr, or.inr ⟨h.left, hr⟩))
    (assume h : (p ∧ q) ∨ (p ∧ r),
      or.elim h
        (assume hpq : p ∧ q, ⟨hpq.left, or.inl hpq.right⟩)
        (assume hpr : p ∧ r, ⟨hpr.left, or.inr hpr.right⟩))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  iff.intro
    (assume h : p ∨ (q ∧ r),
      or.elim h
        (assume hp, ⟨or.inl hp, or.inl hp⟩)
        (assume hqr, ⟨or.inr hqr.left, or.inr hqr.right⟩))
    (assume h : (p ∨ q) ∧ (p ∨ r),
      or.elim h.left
        (assume hp, or.inl hp)
        (assume hq, 
          or.elim h.right
            (assume hp, or.inl hp)
            (assume hr, or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  iff.intro
    (assume h : p → (q → r),
     assume hpq: p ∧ q,
     h hpq.left hpq.right)
    (assume h : p ∧ q → r,
     assume hp : p,
     assume hq : q,
     h ⟨hp, hq⟩)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  iff.intro
    (assume h : p ∨ q → r,
      and.intro
        (assume hp, h (or.inl hp))
        (assume hq, h (or.inr hq)))
    (assume h : (p → r) ∧ (q → r),
     assume hpq : p ∨ q,
     or.elim hpq
      (assume hp, h.left hp)
      (assume hq, h.right hq))
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  iff.intro
    (assume h : ¬(p ∨ q),
      and.intro
        (assume hp, h (or.inl hp))
        (assume hq, h (or.inr hq)))
    (assume h : ¬p ∧ ¬q,
     assume hpq : p ∨ q,
     or.elim hpq
      (assume hp, h.left hp)
      (assume hq, h.right hq))
example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  assume h : ¬p ∨ ¬q,
  assume hpq : p ∧ q,
  or.elim h
    (assume hnp, hnp hpq.left)
    (assume hnq, hnq hpq.right)
example : ¬(p ∧ ¬p) := 
  assume h : p ∧ ¬p,
  h.right h.left
example : p ∧ ¬q → ¬(p → q) := 
  assume h : p ∧ ¬q,
  assume hpq : p → q,
  have hq : q := hpq h.left,
  h.right hq
example : ¬p → (p → q) := 
  assume hnp : ¬p,
  assume hp : p,
  absurd hp hnp
example : (¬p ∨ q) → (p → q) := 
  assume h : ¬p ∨ q,
  assume hp : p,
  or.elim h
    (assume hnp : ¬p, absurd hp hnp)
    (assume hq, hq)
example : p ∨ false ↔ p := 
  iff.intro
    (assume h : p ∨ false,
      or.elim h
        (assume hp, hp)
        (assume f : false, f.elim))
    (assume hp, or.inl hp)
example : p ∧ false ↔ false := 
  iff.intro
    (assume h : p ∧ false, h.right)
    (assume f : false, f.elim)
example : (p → q) → (¬q → ¬p) := 
  assume hpq : p → q,
  assume hnq : ¬q,
  assume hp,
  have hq : q := hpq hp,
  hnq hq

/-
2) Prove the following identities. These require classical reasoning.
-/

open classical

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
  assume h : p → r ∨ s,
  or.elim (em p)
    (assume hp,
      or.elim (h hp)
        (assume hr, or.inl (assume hp, hr))
        (assume hs, or.inr (assume hp, hs)))
    (assume hnp : ¬p,
      or.inl (assume hp, absurd hp hnp))
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  assume h : ¬(p ∧ q),
  or.elim (em p)
    (assume hp, 
      or.elim (em q)
        (assume hq, absurd (and.intro hp hq) h)
        (assume hnq, or.inr hnq))
    (assume hnp, or.inl hnp)
example : ¬(p → q) → p ∧ ¬q := 
  assume h : ¬(p → q),
  by_contradiction
    (assume hn : ¬(p ∧ ¬q),
     or.elim (em q)
      (assume hq, absurd (λ p, hq) h)
      (assume hnq, or.elim (em p)
        (assume hp, absurd (and.intro hp hnq) hn)
        (assume hnp, 
        suffices l : p → q, from h l, 
        assume hp, 
        absurd hp hnp)))
example : (p → q) → (¬p ∨ q) := 
  assume hpq : p → q,
  or.elim (em p)
    (assume hp, or.inr (hpq hp))
    (assume hnp, or.inl hnp)
example : (¬q → ¬p) → (p → q) := 
  assume h : (¬q → ¬p),
  assume hp,
  by_contradiction 
    (assume hnq, have hnp : ¬p := h hnq, hnp hp)
example : p ∨ ¬p := em p
example : ((p → q) → p) → p := 
  assume h : (p → q) → p,
  or.elim (em (p → q))
    (assume h₂ : p → q, h h₂)
    (assume h₂ : ¬(p → q),
      or.elim (em p)
        (assume hp, hp)
        (assume hnp, 
            suffices f : false, from f.elim, 
            suffices h₃ : p → q, from h₂ h₃,
            assume p, absurd p hnp))

/-
3) Prove ¬(p ↔ ¬p) without using classical logic.
-/

example : ¬(p ↔ ¬p) :=
  assume h : p ↔ ¬p,
  suffices hnp : ¬p, from absurd (h.elim_right hnp) hnp, 
  assume hp,
  absurd hp (h.elim_left hp)

/-
4) Show that em can be proved from dne.
-/

example : (∀ q, ¬¬q → q) ↔ (∀ p, p ∨ ¬p) :=
  iff.intro
    (assume h,
     assume q,
     suffices h₂ : ¬¬(q ∨ ¬q), from h (q ∨ ¬q) h₂,
     assume h₂,
     suffices h₃ : q ∨ ¬q, from h₂ h₃,
     or.inr
      (assume hq,
       suffices h₃ : q ∨ ¬q, from h₂ h₃,
       or.inl hq))
    (assume h,
     assume q,
     assume hnnq,
     or.elim (h q)
      (assume hq, hq)
      (assume hnq, absurd hnq hnnq))