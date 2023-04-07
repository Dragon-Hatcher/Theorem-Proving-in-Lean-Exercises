/-
1) Define the function Do_Twice, as described in Section 2.4.
-/

-- Given
def double (x : ℕ) : ℕ := x + x
def square (x : ℕ) := x * x
def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

-- Ex
def quad (x : ℕ) : ℕ := do_twice double x
def times8 (x : ℕ) : ℕ := double (do_twice double x) 
def Do_Twice (f : (ℕ → ℕ) → (ℕ → ℕ)) (g : ℕ → ℕ) : ℕ → ℕ := f (f g)
#reduce Do_Twice do_twice double 2

/-
2) Define the functions curry and uncurry, as described in Section 2.4.
-/

def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := λ a b, f (a, b) 

def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ := λ ab, f ab.1 ab.2 

/-
3) Above, we used the example vec α n for vectors of elements of type α of 
length n. Declare a constant vec_add that could represent a function that 
adds two vectors of natural numbers of the same length, and a constant 
vec_reverse that can represent a function that reverses its argument. Use 
implicit arguments for parameters that can be inferred. Declare some 
variables and check some expressions involving the constants that you have 
declared.
-/

-- Given
universe u
constant vec : Type u → ℕ → Type u

namespace vec
constant empty : Π {α : Type u}, vec α 0
constant cons :
  Π {α : Type u} {n : ℕ}, α → vec α n → vec α (n + 1)
constant append :
  Π {α : Type u} {n m : ℕ},  vec α m → vec α n → vec α (n + m)

constant add : Π {n : ℕ}, (vec nat n) → (vec nat n) → vec nat n
constant reverse : Π {α : Type u} {n : ℕ}, (vec α n) → vec α n

#check add empty empty
#check add (cons 1 empty) (cons 2 empty)
#check reverse empty
#check reverse (cons 1 (cons 2 empty))

end vec

/-
4) Similarly, declare a constant matrix so that matrix α m n could represent 
the type of m by n matrices. Declare some constants to represent functions 
on this type, such as matrix addition and multiplication, and (using vec) 
multiplication of a matrix by a vector. Once again, declare some variables 
and check some expressions involving the constants that you have declared.
-/

constant matrix : Type u → ℕ → ℕ → Type u

namespace matrix

constant zero_by : Π {α : Type u} {m : ℕ}, matrix α 0 m
constant add_row : Π {α : Type u} {n m : ℕ}, matrix α n m → vec α m → matrix α (n + 1) m

constant add : Π {α : Type u} {n m : ℕ}, matrix α n m → matrix α n m → matrix α n m
constant mul : Π {α : Type u} {n m p : ℕ}, matrix α n m → matrix α m p → matrix α m p
constant mul_vec : Π {α : Type u} {n m : ℕ}, matrix α n m → vec α n → matrix α n m

constant m2x2 : matrix nat 2 2
constant m3x2 : matrix nat 3 2
constant m2x3 : matrix nat 2 3
constant v2 : vec nat 2

#check add m2x2 m2x2
#check mul m2x3 m3x2
#check mul_vec m2x2 v2

end matrix
