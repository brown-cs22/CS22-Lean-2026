import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs
import AutograderLib

-- don't change these lines
namespace Rec03
open Set BrownCs22.Set
variable (U : Type)
variable (A B : Set U)

/-

# Welcome to the Lean section of Recitation 3!

In these problems, we're going to get a little practice formally proving the
set equalities from Tasks 3 and 4 in Recitation 3.

* With the set-element method (Task 3), we argue that `A = B` by showing that
  `A ⊆ B` and `B ⊆ A`.
* With the algebraic method (Task 4), we can prove that sets are equal by rewriting
  one or both sides with algebraic identities like `(Aᶜ)ᶜ = A`, until we
  have identical expressions.

In this assignment you'll prove the set equality from Task 3, Part a using the set
equivalence method and the set equality from Task 4, Part a with the set algebra
method.

**Notes**:

* Remember that in Lean, we write "the complement of A" as `Aᶜ` instead
  of using a bar over the letter. (Diacritics are hard in a text editor!)

* You can type `⊆` using `\sub`.

* You can type `ᶜ` using `\compl` or `\^c`.

-/


/-

## Problem 1: the set element method (Task 3, Part a)

We saw two important tactics in lecture for set-element proofs in Lean:

* `extensionality`: given a goal `A = B` where `A` and `B` are sets,
  changes the goal to showing `∀ x, x ∈ A ↔ x ∈ B`.
  The name "extensionality" refers to the property that two sets are equal
  if they have the same elements.

* `set_simplify`: unfolds the "logic" of a set membership proposition.
  For instance, `x ∈ A ∩ B` simplifies to `x ∈ A ∧ x ∈ B`.
  `x ∈ A \ C` simplifies to `x ∈ A ∧ ¬(x ∈ C)`.
  Calling `set_simplify` will simplify the goal and all hypotheses.

Use these techniques to prove the following.
Starting with `extensionality` is probably a good move!
Then think about the last few homeworks; how do you prove an `↔` goal?

-/

theorem problem_1 : 𝒫(A ∩ B) ⊆ 𝒫(A) := by
--sol   sorry
  fix X
  assume hXinter
  set_simplify
  fix x
  assume hxX
  rewrite subset_def at hXinter
  have hxAB : x ∈ A ∩ B := hXinter x hxX
  set_simplify
  eliminate hxAB with hxA hxB
  assumption
  --los
  done


/-

## Problem 2: the algebraic method (Task 4, Part a)

In this recitation, you saw a list of set identities:
<https://brown-cs22.github.io/resources/math-resources/sets.pdf>
All the identities on this list are available as rewrite rules in Lean,
listed in the file `BrownCs22/Demos/SetIdentities.lean`.

Use these rewrite rules to complete the following proof. Your proof should
have a sequence of rewrites, followed by `reflexivity`.

Use the work you did on paper/LaTeX to solve this!

-/

theorem problem_2 : (A ∩ Bᶜ) ∪ B = A ∪ B := by
--sol   sorry
  rewrite inter_union_distrib_right
  rewrite union_comm Bᶜ B
  rewrite union_compl_self
  rewrite inter_univ
  reflexivity
--los
  done

end Rec03
