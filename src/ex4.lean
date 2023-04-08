import data.nat.basic
import data.int.basic
import data.real.basic

/-
1) Prove these equivalences:
-/

variables (α : Type*) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  iff.intro
    (assume h,
     and.intro
      (assume a, (h a).left)
      (assume a, (h a).right))
    (assume h,
     assume a,
     have hpa : p a := h.left a,
     have hqa : q a := h.right a,
     ⟨hpa, hqa⟩)
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  assume h₁,
  assume h₂,
  assume a,
  h₁ a (h₂ a)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  assume h,
  assume a,
  or.elim h
    (assume hp, or.inl (hp a))
    (assume hq, or.inr (hq a))

/-
You should also try to understand why the reverse implication is not derivable in 
the last example.
-/

/-
It could be that e.g. p x for half of x and q x for the other half whereas the
condition requires that it is 100% one way or the other
-/

/-
2) It is often possible to bring a component of a formula outside a universal 
quantifier, when it does not depend on the quantified variable. Try proving these 
(one direction of the second of these requires classical logic):
-/

variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
  assume a,
  iff.intro 
    (assume h, h a)
    (assume r, assume _, r)
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
  iff.intro
    (assume h₁,
    or.elim (em r)
      (assume hr, or.inr hr)
      (assume hnr, or.inl 
        (assume a,
         have h₂ : _ := h₁ a,
         or.elim h₂
          (assume hp, hp)
          (assume hr, absurd hr hnr))))
    (assume h₁,
     or.elim h₁
      (assume h₂, assume a, or.inl (h₂ a))
      (assume hr, assume _, or.inr hr))
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
  iff.intro
    (assume h,
     assume hr,
     assume a,
     h a hr)
    (assume h,
     assume a,
     assume hr,
     h hr a)

/-
3) Consider the “barber paradox,” that is, the claim that in a certain town there is 
a (male) barber that shaves all and only the men who do not shave themselves. Prove 
that this is a contradiction:
-/

variables (men : Type*) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := 
  have h₂ : _ := h barber,
  suffices hn₃ : ¬shaves barber barber, from 
    (have h₃ : shaves barber barber := h₂.elim_right hn₃,
     hn₃ h₃),
  assume hsbb,
  have hnsbb : _ := h₂.elim_left hsbb,
  hnsbb hsbb

/-
4) Remember that, without any parameters, an expression of type Prop is just an 
assertion. Fill in the definitions of prime and Fermat_prime below, and construct 
each of the given assertions. For example, you can say that there are infinitely many 
primes by asserting that for every natural number n, there is a prime number greater 
than n. Goldbach’s weak conjecture states that every odd number greater than 5 is the 
sum of three primes. Look up the definition of a Fermat prime or any of the other 
statements, if necessary.
-/

#check @even

def prime (n : ℕ) : Prop := ¬∃ x y, x > 1 ∧ y > 1 ∧ x * y = n

def infinitely_many_primes : Prop := ∀ n, ∃ m, m > n ∧ prime m

-- 2^(2^n) + 1
def Fermat_prime (n : ℕ) : Prop := prime n ∧ (∃ m : ℕ, 2 ^ (2 ^ m) + 1 = n)  

def infinitely_many_Fermat_primes : Prop := ∀ n, ∃ m, m > n ∧ Fermat_prime m

-- all p > 2 is sum of two ps 
def goldbach_conjecture : Prop := ∀ p, p > 2 → ∃ a b, prime a ∧ prime b ∧ a + b = p      

def Goldbach's_weak_conjecture : Prop := 
  ∀ p, p > 5 → ¬even p → ∃ a b c, prime a ∧ prime b ∧ prime c ∧ a + b + c = p

def Fermat's_last_theorem : Prop := 
  ¬∃ n, n > 2 ∧ (∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^n + b^n = c^n) 

/-
5) Prove as many of the identities listed in Section 4.4 as you can.
-/

open classical

example : (∃ x : α, r) → r := 
  assume h,
  let ⟨a, hr⟩ := h in
  hr
example (a : α) : r → (∃ x : α, r) := 
  assume hr,
  exists.intro a hr
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  iff.intro
    (assume h₁,
     let ⟨a, h₂⟩ := h₁ in
     ⟨⟨a, h₂.left⟩, h₂.right⟩)
    (assume h₁,
     let ⟨h₂, hr⟩ := h₁ in
     let ⟨a, hp⟩ := h₂ in
     ⟨a, ⟨hp, hr⟩⟩)
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  iff.intro
    (assume h₁,
     let ⟨a, h₂⟩ := h₁ in
     or.elim h₂
      (assume hp, or.inl ⟨a, hp⟩)
      (assume hq, or.inr ⟨a, hq⟩))
    (assume h₁,
     or.elim h₁
      (assume h₂,
       let ⟨a, hp⟩ := h₂ in
       ⟨a, or.inl hp⟩)
      (assume h₂,
       let ⟨a, hq⟩ := h₂ in
       ⟨a, or.inr hq⟩))
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  iff.intro
    (assume h₁,
     assume h₂,
     let ⟨a, hnp⟩ := h₂ in
     have hp : p a := h₁ a,
     hnp hp)
    (assume h₁,
     assume a,
     or.elim (classical.em (p a))
      (assume hpa, hpa)
      (assume hnpa, 
       have hn₁ : ∃ (x : α), ¬p x := ⟨a, hnpa⟩,
       absurd hn₁ h₁))
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  iff.intro
    (assume h₁,
     assume h₂,
     let ⟨a, h₃⟩ := h₁ in
     have hn₃ : ¬p a, from h₂ a,
     hn₃ h₃)
    (assume h₁,
     or.elim (classical.em ∃ (x : α), p x)
      (assume h₂, h₂)
      (assume h₂,
       suffices f : false, from f.elim,
       suffices hn₁ : ∀ (x : α), ¬p x, from h₁ hn₁,
       assume a,
       assume hp,
       h₂ ⟨a, hp⟩))
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
  iff.intro
    (assume h₁,
     assume a,
     assume hp,
     h₁ ⟨a, hp⟩)
    (assume h₁,
     assume h₂,
     let ⟨a, hp⟩ := h₂ in
     have hnp : ¬p a := h₁ a,
     hnp hp)
    --  
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
  iff.intro
    (assume h₁,
     or.elim (classical.em ∃ (x : α), ¬p x)
      (assume h₂, h₂)
      (assume h₂, 
       suffices f : false, from f.elim,
       suffices hn₁ : ∀ (x : α), p x, from h₁ hn₁,
       assume a,
       or.elim (classical.em (p a))
        (assume hpa, hpa)
        (assume hnpa, 
         have hn₂ : ∃ x, ¬p x, from ⟨a, hnpa⟩,
         absurd hn₂ h₂)))
    (assume h₁,
     assume h₂,
     let ⟨a, hnp⟩ := h₁ in
     have hp : _ := h₂ a,
     hnp hp)
example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  iff.intro
    (assume h₁,
     assume h₂,
     let ⟨a, h₃⟩ := h₂ in
     h₁ a h₃)
    (assume h₁,
     assume a,
     assume hpa,
     h₁ ⟨a, hpa⟩)
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  iff.intro
    (assume h₁,
     assume h₂,
     let ⟨a₂, h₃⟩ := h₁ in
     h₃ (h₂ a₂))
    (assume h₁,
  or.elim (classical.em (∀ (x : α), p x))
    (assume h₂,
     have hr : r := h₁ h₂,
     ⟨a, assume _, hr⟩)
    (assume h₂,
     have h₃ : ∃ x, ¬ p x := 
      (or.elim (classical.em ∃ (x : α), ¬p x)
        (assume x, x)
        (assume h₄,
        suffices f : false, from f.elim,
        suffices hn₁ : ∀ (x : α), p x, from h₂ hn₁,
        assume ha,
        or.elim (classical.em (p ha))
          (assume x, x)
          (assume hnpa, 
           have hn₄ : ∃ x, ¬p x, from ⟨ha, hnpa⟩,
           absurd hn₄ h₄))),
     let ⟨a₂, h₄⟩ := h₃ in
     ⟨a₂, assume hn₄, absurd hn₄ h₄⟩))
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
  iff.intro
    (assume h₁,
     assume hr,
     let ⟨a, h₂⟩ := h₁ in
     ⟨a, h₂ hr⟩)
    (assume h₁,
     or.elim (classical.em r)
      (assume hr,
       have h₂ : _ := h₁ hr,
       let ⟨a2, hp⟩ := h₂ in
       ⟨a2, assume hr, hp⟩)
      (assume hnr,
       ⟨a, assume hr, absurd hr hnr⟩))

/-
6) Give a calculational proof of the theorem log_mul below.
-/

variables log exp    : real → real
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc log (x * y) = log (exp (log x) * exp (log y)) : by rw [exp_log_eq hx, exp_log_eq hy]
             ... = log (exp (log x + log y))       : by rw ← exp_add
             ... = log x + log y                   : by rw log_exp_eq  

/-
7) Prove the theorem below, using only the ring properties of ℤ enumerated in 
 Section 4.2 and the theorem sub_self.
-/

#check sub_self

example (x : ℤ) : x * 0 = 0 :=
 calc x * 0 = x * (x - x)   : by rw sub_self
        ... = x * x - x * x : by rw mul_sub
        ... = 0             : by rw sub_self