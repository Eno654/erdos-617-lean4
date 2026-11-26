module

public section

/-!
# Advertised Statements — Erdős Problem #617 (`r^2` Infinitude and `r = 3` on K_10)

This file is the small, zero-dependency, human-auditable statement surface checked by
`lake comparator` against `Solution.lean`. Every declaration uses only Lean 4 core primitives
(`Nat`, `Fin`, `List`, `List.Pairwise`) with zero custom definitions.

Reference:
- P. Erdős and A. Gyárfás, "Split and balanced colorings of complete graphs",
  Discrete Mathematics 200 (1999), 79–86.
- https://www.erdosproblems.com/617
-/

namespace Erdos617

/--
Erdős Problem #617 (`erdos_617.variants.r2`, Erdős–Gyárfás 1999):
For arbitrarily large `r` (specifically every prime `p ≥ N`), there exists a symmetric
`p`-coloring of the complete graph on `p^2` vertices (`Fin p × Fin p`) such that every
list of `p + 1` pairwise distinct vertices contains an edge of every color `k : Fin p`.
-/
theorem erdos_617_variants_r2 :
    ∀ N : Nat, ∃ p : Nat, N ≤ p ∧ (2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p) ∧
      ∃ c : (Fin p × Fin p) → (Fin p × Fin p) → Fin p,
        (∀ u v, c u v = c v u) ∧
        (∀ (S : List (Fin p × Fin p)), S.Pairwise (· ≠ ·) → S.length = p + 1 →
          ∀ k : Fin p, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c u v = k) := by
  sorry

/--
Erdős Problem #617 (`erdos_617.variants.r_eq_3`, Erdős–Gyárfás 1999):
Every symmetric 3-coloring of the complete graph `K_10` (`Fin 10`) contains 4 pairwise
distinct vertices whose 6 induced edges miss at least one color `k : Fin 3`.
-/
theorem erdos_617_variants_r_eq_3 (c : Fin 10 → Fin 10 → Fin 3)
    (hsymm : ∀ u v, c u v = c v u) :
    ∃ (a b d e : Fin 10) (k : Fin 3),
      a ≠ b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e ∧
      c a b ≠ k ∧ c a d ≠ k ∧ c a e ≠ k ∧ c b d ≠ k ∧ c b e ≠ k ∧ c d e ≠ k := by
  sorry

end Erdos617
