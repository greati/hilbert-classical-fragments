/- Comment -/

-- comment

-- declaring objects
constants m n : nat
constant f : nat → nat
constant p : prod nat nat

#check (m, n)
#check p.1

-- types are objects
#check nat

constants α β : Type
constant F : Type → Type

#check α
#check F α

-- of what type is the type Type?
#check Type
#check Type 1
#check Type 2
--...

-- Prop is a special type
#check Prop

-- Polymorphic types
#check list
#check prod
-- in order to create polymorphic types, one must use universe variables
universe u
constant γ : Type u
#check γ

-- besides of application, abstraction (creating functions from other ones) comes into play when dealing with functions
#check λ x : nat, x + 5
#check λ x : nat, x + 7
-- we can rely on type inference
#check λ x, x + 8

-- expressions that are the same up to renaming of bound variables are called alpha equivalent
-- the process of simplifying an expression (λ x, t) s to t[s/x] is known as beta reduction, and
-- two terms that reduce to a common term are called beta equivalent
#reduce (m, n).1

-- important feature of dependent type theory: every term has a computational behaviour, and supports a notion of
-- reduction, or normalization. In principle, two terms that reduce to the same value are called
-- definitionally equal

-- this computation behaviour makes it possible to use Lean as a programming language as well
#eval 1234*1234

-- constant allows to declare objects, but how can we define them?

def foo : (ℕ → ℕ) → ℕ := λ f, f 0

#check foo
#print foo

-- alternative notation
def double (x : ℕ) : ℕ := x + x

-- local definitions
