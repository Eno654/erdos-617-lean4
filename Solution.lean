module

public import Erdos617

public section

/-!
# Proved Solutions — Erdős Problem #617 (`r^2` Infinitude and `r = 3` on K_10)

Comparator verifies that every theorem below matches its declaration in `Challenge.lean`
exactly and depends only on `[propext, Quot.sound, Classical.choice]`.
-/

namespace Erdos617

theorem erdos_617_variants_r2 :
    ∀ N : Nat, ∃ p : Nat, N ≤ p ∧ (2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p) ∧
      ∃ c : (Fin p × Fin p) → (Fin p × Fin p) → Fin p,
        (∀ u v, c u v = c v u) ∧
        (∀ (S : List (Fin p × Fin p)), S.Pairwise (· ≠ ·) → S.length = p + 1 →
          ∀ k : Fin p, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c u v = k) :=
  Erdos617R2.erdos_617_variants_r2_infinite

theorem erdos_617_variants_r_eq_3 (c : Fin 10 → Fin 10 → Fin 3)
    (hsymm : ∀ u v, c u v = c v u) :
    ∃ (a b d e : Fin 10) (k : Fin 3),
      a ≠ b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e ∧
      c a b ≠ k ∧ c a d ≠ k ∧ c a e ≠ k ∧ c b d ≠ k ∧ c b e ≠ k ∧ c d e ≠ k :=
  Erdos617R3.erdos_617_variants_r_eq_3 c hsymm

end Erdos617
