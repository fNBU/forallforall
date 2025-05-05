import Mathlib.Tactic

inductive Tree' where
  | empty
  | node : Tree' -> Tree' -> Tree'

open Tree'

def nodes ( t : Tree' ) : Nat :=
  match t with
    | empty => 1
    | node x y => 1 + nodes x + nodes y

def explode ( n : Nat ) ( t : Tree' ) : Tree' :=
  match n with
    | 0 => t
    | k + 1 => explode k ( node t t )

-- In the proof below, I write the goal on the right in a comment.

-- Here is how dependent types show up in the following:
-- - `∀ n , ∀ t , nodes ( explode n t ) = 2^n * ( 1 + nodes t) - 1` is a
--   dependent type `Nat -> Tree' -> Prop`. Think of `Prop` like `Type`.
-- - the tactic `intro` binds a name to a function argument (which
--   includes the arguments of dependent types since they are just
--   functions).
-- - the case `succ n ih` also binds names (by pattern matching), but
--   there are two things in the context to bind: the induction variable
--   and the induction hypothesis.
-- - `ih` is `∀ (t : Tree'), nodes (explode n t) = 2 ^ n * (1 + nodes t) - 1`
--   which is a dependent type. We can provide it a particular `Tree'`
--   just as we would a function argument, and obtain it with that `Tree'`
--   substituted. This happens at `rw [ ih ( node t' t' ) ]`.
-- - `(t'.node t')` is sugar for `( node t' t' )`
-- - `ring_nf` is the only place where I use the Mathlib import.

example : ∀ n , ∀ t , nodes ( explode n t ) = 2^n * ( 1 + nodes t) - 1 := by
  intro n
  induction n with             -- ⊢ ∀ (t : Tree'), nodes (explode n t) = 2 ^ n * (1 + nodes t) - 1
  | zero =>                    -- ⊢ ∀ (t : Tree'), nodes (explode 0 t) = 2 ^ 0 * (1 + nodes t) - 1
    unfold explode             -- ⊢ ∀ (t : Tree'), nodes t = 2 ^ 0 * (1 + nodes t) - 1
    simp_all +arith            -- no goals
  | succ n ih =>               -- ⊢ ∀ (t : Tree'), nodes (explode (n + 1) t) = 2 ^ (n + 1) * (1 + nodes t) - 1
    unfold explode             -- ⊢ ∀ (t : Tree'), nodes (explode n (t.node t)) = 2 ^ (n + 1) * (1 + nodes t) - 1
    intro t'                   -- ⊢ nodes (explode n (t'.node t')) = 2 ^ (n + 1) * (1 + nodes t') - 1
    rw [ ih ( node t' t' ) ]   -- ⊢ 2 ^ n * (1 + nodes (t'.node t')) - 1 = 2 ^ (n + 1) * (1 + nodes t') - 1
    rw [ nodes ]                -- ⊢ 2 ^ n * (1 + (1 + nodes t' + nodes t')) - 1 = 2 ^ (n + 1) * (1 + nodes t') - 1
    ring_nf                    -- no goals
