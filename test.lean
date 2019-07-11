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
-- in order to create polymorphic types, one must use universe variables,
-- where these variables range over the level of types
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

-- local definitions, using the let construct
#check let y := 2 in y + y

def bar := (λ a : Type, λ x : a, x) nat -- works, because the expression doesn't depend on the value of a
--def bar := (λ a : Type, λ x : a, x+2) nat -- doesn't work, because x+2 doesn't make sense for every value of a

-- it is better to use variables instead of extending the system with new constants
-- for that, there are the local declarations and the variable and variables constructs
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)

variable k : ℕ
def my_double := 2 * k

-- sections can help to define scopes
-- namespaces can be used to group definitions
-- the construct open allow to use the names inside a namespace

-- dependent type theory: types can depend on parameters
-- Pi type or dependent function type: Π x:α, β x means 
-- the type of all functions f which when take a value x
-- of type α, return a value of type β x

namespace hidden

universe v

constant list : Type v → Type v

constant cons : Π α : Type u, α → list α → list α

#check list ℕ

end hidden

-- seamingly, sigma types generalize the notion of products,
-- such that the type of the second element depends on
-- the type of the first element

-- implicit arguments: type inference over dependent types
-- use _ to hide the type and let the type inference mechanism act
-- use { } when declaring a parameter, and this will default to
-- always use the type inference mechanism
-- { } works also on variables/variable declarations

-- tactics mode
-- tactics are instructions that tell Lean how to construct a proof term
-- tactics-style contrasts with term-style
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
    apply and.intro,
    exact hp,
    apply and.intro,
    exact hq,
    exact hp
end

#print test

-- one can use the by keyword when there is only one
-- step for the proof
-- the include command tells lean to include the indicated variables
-- the omit keywork limit the effect of an include
-- examples of tactics: apply, exact, intro, reflexivity, symmetry, transitivity
-- assumption, repeat, fapply, revert, generalize, sorry, rewrite, left, right,
-- cases, constructor, existsi, split, induction, contradiction
