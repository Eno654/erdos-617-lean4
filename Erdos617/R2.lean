module

@[expose] public section

/-
Standalone Lean 4 (v4.36.0) Formal Proof — Zero external imports, zero sorry, zero custom axioms.
Proves the core mathematical theorem of Erdős Problem #617 (`erdos_617.variants.r2`, Erdős–Gyárfás 1999):
For infinitely many r (every prime p), there exists a symmetric edge-coloring of K_{r^2} with r colors
such that every subset of r + 1 distinct vertices contains an edge of every color k : Fin r.
-/

namespace Erdos617R2

def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-! ### Part 1: Elementary Modular Arithmetic over Nat -/

theorem dvd_of_add_mod_eq {a b p : Nat} (_hp : 0 < p) (h : (a + b) % p = a % p) : p ∣ b := by
  have h1 := Nat.div_add_mod a p
  have h2 := Nat.div_add_mod (a + b) p
  have hle : a / p ≤ (a + b) / p := Nat.div_le_div_right (Nat.le_add_right a b)
  refine ⟨(a + b) / p - a / p, ?_⟩
  rw [Nat.mul_sub_left_distrib]
  omega

theorem mod_eq_of_add_mod_eq {a b c p : Nat} (hp : 0 < p)
    (h : (a + b) % p = (a + c) % p) : b % p = c % p := by
  have h1 := Nat.div_add_mod (a + b) p
  have h2 := Nat.div_add_mod (a + c) p
  have h3 := Nat.div_add_mod b p
  have h4 := Nat.div_add_mod c p
  have h5 := Nat.mod_lt b hp
  have h6 := Nat.mod_lt c hp
  have hb : (a + b) % p = (a % p + b % p) % p := Nat.add_mod a b p
  have hc : (a + c) % p = (a % p + c % p) % p := Nat.add_mod a c p
  rw [hb, hc] at h
  have hltA : a % p < p := Nat.mod_lt a hp
  by_cases h1b : a % p + b % p < p
  · by_cases h1c : a % p + c % p < p
    · rw [Nat.mod_eq_of_lt h1b, Nat.mod_eq_of_lt h1c] at h
      omega
    · have h1c' : (a % p + c % p) % p = a % p + c % p - p := by
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt h1c)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [Nat.mod_eq_of_lt h1b, h1c'] at h
      omega
  · have h1b' : (a % p + b % p) % p = a % p + b % p - p := by
      rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt h1b)]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases h1c : a % p + c % p < p
    · rw [h1b', Nat.mod_eq_of_lt h1c] at h
      omega
    · have h1c' : (a % p + c % p) % p = a % p + c % p - p := by
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt h1c)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1b', h1c'] at h
      omega

theorem prime_coprime_of_lt {p a : Nat} (hp : IsPrime p) (ha0 : 0 < a) (hap : a < p) :
    Nat.Coprime p a := by
  unfold Nat.Coprime
  have hdvd : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  cases hp.2 (Nat.gcd p a) hdvd with
  | inl h1 => exact h1
  | inr hp' =>
    have hpa : p ∣ a := by
      rw [← hp']
      exact Nat.gcd_dvd_right p a
    have hle : p ≤ a := Nat.le_of_dvd ha0 hpa
    omega

theorem mod_mul_unique {p dx m1 m2 : Nat} (hp : IsPrime p)
    (hdx0 : 0 < dx) (hdxp : dx < p) (hm1 : m1 < p) (hm2 : m2 < p)
    (heq : (m1 * dx) % p = (m2 * dx) % p) : m1 = m2 := by
  have hp0 : 0 < p := by have := hp.1; omega
  have hcop : Nat.Coprime p dx := prime_coprime_of_lt hp hdx0 hdxp
  cases Nat.le_total m1 m2 with
  | inl hle =>
    have hadd : m2 * dx = m1 * dx + (m2 - m1) * dx := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hle]
    rw [hadd] at heq
    have hdvd : p ∣ (m2 - m1) * dx := dvd_of_add_mod_eq hp0 heq.symm
    have hdvd_diff : p ∣ (m2 - m1) := hcop.dvd_of_dvd_mul_right hdvd
    by_cases h0 : m2 - m1 = 0
    · omega
    · have hge := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd_diff
      omega
  | inr hle =>
    have hadd : m1 * dx = m2 * dx + (m1 - m2) * dx := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hle]
    rw [hadd] at heq
    have hdvd : p ∣ (m1 - m2) * dx := dvd_of_add_mod_eq hp0 heq
    have hdvd_diff : p ∣ (m1 - m2) := hcop.dvd_of_dvd_mul_right hdvd
    by_cases h0 : m1 - m2 = 0
    · omega
    · have hge := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd_diff
      omega

/-! ### Part 2: Euclid's Infinitude of Primes -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n : Nat, 0 < fact n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

theorem dvd_fact {k n : Nat} (hk : 0 < k) (hkn : k ≤ n) : k ∣ fact n := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold fact
    cases Nat.eq_or_lt_of_le hkn with
    | inl heq =>
      rw [heq]
      exact Nat.dvd_mul_right (n + 1) (fact n)
    | inr hlt =>
      exact Nat.dvd_trans (ih (Nat.le_of_lt_succ hlt)) (Nat.dvd_mul_left (fact n) (n + 1))

def minDivAux (n d : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n % d == 0 then d else minDivAux n (d + 1) fuel

theorem minDivAux_dvd {n d fuel : Nat} (hd : 0 < d) : minDivAux n d fuel ∣ n := by
  induction fuel generalizing d with
  | zero => exact Nat.dvd_refl n
  | succ fuel ih =>
    unfold minDivAux
    by_cases h : (n % d == 0) = true
    · simp only [h, ite_true]
      exact Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h)
    · simp only [h]
      exact ih (by omega)

theorem minDivAux_ge {n d fuel : Nat} (hdn : d ≤ n) : d ≤ minDivAux n d fuel := by
  induction fuel generalizing d with
  | zero => exact hdn
  | succ fuel ih =>
    unfold minDivAux
    by_cases h : (n % d == 0) = true
    · simp only [h, ite_true]
      exact Nat.le_refl d
    · simp only [h]
      have hne : d ≠ n := by
        intro heq
        subst heq
        have h0 : (d % d == 0) = true := beq_iff_eq.mpr (Nat.mod_self d)
        exact h h0
      exact Nat.le_trans (Nat.le_succ d) (ih (by omega))

theorem minDivAux_min {n d fuel k : Nat} (hdk : d ≤ k) (hkl : k < d + fuel) (hdvd : k ∣ n) :
    minDivAux n d fuel ≤ k := by
  induction fuel generalizing d with
  | zero => omega
  | succ fuel ih =>
    unfold minDivAux
    by_cases h : (n % d == 0) = true
    · simp only [h, ite_true]
      exact hdk
    · simp only [h]
      have hne : d ≠ k := by
        intro heq
        subst heq
        have h0 : (n % d == 0) = true := beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hdvd)
        exact h h0
      exact ih (by omega) (by omega)

theorem exists_prime_ge (N : Nat) : ∃ p : Nat, N ≤ p ∧ IsPrime p := by
  let M := fact N + 1
  have hM2 : 2 ≤ M := by
    have := fact_pos N
    omega
  let p := minDivAux M 2 M
  have hp_dvd : p ∣ M := minDivAux_dvd (by omega)
  have hp_ge2 : 2 ≤ p := minDivAux_ge hM2
  have hp_prime : IsPrime p := by
    refine ⟨hp_ge2, ?_⟩
    intro d hd_dvd
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · right
      have hd0 : 0 < d := by
        cases d with
        | zero =>
          rcases hd_dvd with ⟨q, hq⟩
          simp at hq
          omega
        | succ _ => exact Nat.succ_pos _
      have hd2 : 2 ≤ d := by omega
      have hd_dvd_M : d ∣ M := Nat.dvd_trans hd_dvd hp_dvd
      have hp_pos : 0 < p := by omega
      have hd_le_p : d ≤ p := Nat.le_of_dvd hp_pos hd_dvd
      have hd_le_M : d ≤ M := Nat.le_of_dvd (by omega) hd_dvd_M
      have hp_le_d : p ≤ d := minDivAux_min hd2 (by omega) hd_dvd_M
      omega
  have hp_geN : N ≤ p := by
    by_cases hlt : p < N
    · exfalso
      have hp_dvd_fact : p ∣ fact N := dvd_fact (by omega) (Nat.le_of_lt hlt)
      rcases hp_dvd with ⟨a, ha⟩
      rcases hp_dvd_fact with ⟨b, hb⟩
      have h1 : p * (a - b) = 1 := by
        rw [Nat.mul_sub_left_distrib]
        omega
      have hle : p ≤ 1 := by
        cases hsub : a - b with
        | zero =>
          rw [hsub, Nat.mul_zero] at h1
          exact absurd h1 (by decide)
        | succ k =>
          rw [hsub] at h1
          have hge : p ≤ p * (k + 1) := Nat.le_mul_of_pos_right p (Nat.succ_pos k)
          omega
      omega
    · omega
  exact ⟨p, hp_geN, hp_prime⟩

/-! ### Part 3: Pigeonhole Principle on Lists -/

theorem exists_pair_of_count_ge_two {α : Type} (l : List α) (P : α → Bool)
    (hcnt : 2 ≤ (l.filter P).length) :
    ∃ (u v : α), u ∈ l ∧ v ∈ l ∧ P u = true ∧ P v = true ∧
      (l.Pairwise (· ≠ ·) → u ≠ v) := by
  induction l with
  | nil => simp at hcnt
  | cons a t ih =>
    by_cases hPa : P a = true
    · simp [List.filter, hPa] at hcnt
      have hne : (t.filter P).length ≥ 1 := by omega
      cases htf : t.filter P with
      | nil => simp [htf] at hne
      | cons b rest =>
        have hb_mem : b ∈ t.filter P := by rw [htf]; exact List.mem_cons_self
        have hb_t : b ∈ t := (List.mem_filter.mp hb_mem).1
        have hPb : P b = true := (List.mem_filter.mp hb_mem).2
        refine ⟨a, b, List.mem_cons_self, List.mem_cons_of_mem a hb_t, hPa, hPb, ?_⟩
        intro hpw
        exact (List.pairwise_cons.mp hpw).1 b hb_t
    · have hPaF : P a = false := Bool.eq_false_iff.mpr hPa
      simp [List.filter, hPaF] at hcnt
      rcases ih hcnt with ⟨u, v, hu, hv, hPu, hPv, hne⟩
      refine ⟨u, v, List.mem_cons_of_mem a hu, List.mem_cons_of_mem a hv, hPu, hPv, ?_⟩
      intro hpw
      exact hne (List.pairwise_cons.mp hpw).2

theorem filter_length_add_not {α : Type} (l : List α) (P : α → Bool) :
    (l.filter P).length + (l.filter (fun x => !P x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hPa : P a <;> simp [List.filter, hPa] <;> omega

theorem list_pigeonhole {α : Type} :
    ∀ (p : Nat) (l : List α) (f : α → Nat),
      l.Pairwise (· ≠ ·) →
      (∀ x ∈ l, f x < p) →
      p < l.length →
      ∃ u ∈ l, ∃ v ∈ l, u ≠ v ∧ f u = f v := by
  intro p
  induction p with
  | zero =>
    intro l f _ hlt hlen
    cases l with
    | nil => simp at hlen
    | cons a _ =>
      have := hlt a List.mem_cons_self
      omega
  | succ p ih =>
    intro l f hpw hlt hlen
    let P : α → Bool := fun x => decide (f x = p)
    by_cases h2 : 2 ≤ (l.filter P).length
    · rcases exists_pair_of_count_ge_two l P h2 with ⟨u, v, hu, hv, hPu, hPv, hne⟩
      have hfu : f u = p := of_decide_eq_true hPu
      have hfv : f v = p := of_decide_eq_true hPv
      exact ⟨u, hu, v, hv, hne hpw, hfu.trans hfv.symm⟩
    · let l' := l.filter (fun x => !P x)
      have hsum := filter_length_add_not l P
      have hlen' : p < l'.length := by
        dsimp [l']
        omega
      have hpw' : l'.Pairwise (· ≠ ·) := hpw.filter _
      have hlt' : ∀ x ∈ l', f x < p := by
        intro x hx
        have hx1 := List.mem_filter.mp hx
        have hlt_succ := hlt x hx1.1
        have hne_p : f x ≠ p := by
          intro heq
          have hP : P x = true := decide_eq_true heq
          have hnot : (!P x) = true := hx1.2
          rw [hP] at hnot
          cases hnot
        omega
      rcases ih l' f hpw' hlt' hlen' with ⟨u, hu, v, hv, hne, heq⟩
      exact ⟨u, (List.mem_filter.mp hu).1, v, (List.mem_filter.mp hv).1, hne, heq⟩

/-! ### Part 4: Surjectivity of Multiplication Mod Prime via Pigeonhole -/

theorem list_range_pairwise_ne (n : Nat) : (List.range n).Pairwise (· ≠ ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    simp at hb
    subst hb
    have hlt := List.mem_range.mp ha
    omega

theorem prime_mul_surjective {p dx dy : Nat} (hp : IsPrime p)
    (hdx0 : 0 < dx) (hdxp : dx < p) (hdy : dy < p) :
    ∃ m : Nat, m < p ∧ (m * dx) % p = dy := by
  by_cases hex : ∃ m : Nat, m < p ∧ (m * dx) % p = dy
  · exact hex
  · exfalso
    have hp0 : 0 < p := by have := hp.1; omega
    let g : Nat → Nat := fun k => if k < p then (k * dx) % p else dy
    have hlt : ∀ k ∈ List.range (p + 1), g k < p := by
      intro k _
      show (if k < p then (k * dx) % p else dy) < p
      split
      · exact Nat.mod_lt _ hp0
      · exact hdy
    have hlen : p < (List.range (p + 1)).length := by simp
    rcases list_pigeonhole p (List.range (p + 1)) g (list_range_pairwise_ne (p + 1)) hlt hlen with
      ⟨u, hu, v, hv, hne, hge⟩
    have hu_lt : u < p + 1 := List.mem_range.mp hu
    have hv_lt : v < p + 1 := List.mem_range.mp hv
    by_cases hup : u < p
    · by_cases hvp : v < p
      · simp only [g, hup, hvp, ite_true] at hge
        exact hne (mod_mul_unique hp hdx0 hdxp hup hvp hge)
      · simp only [g, hup, hvp, ite_true, ite_false] at hge
        exact hex ⟨u, hup, hge⟩
    · by_cases hvp : v < p
      · simp only [g, hup, hvp, ite_true, ite_false] at hge
        exact hex ⟨v, hvp, hge.symm⟩
      · omega

/-! ### Part 5: Affine-Plane Coloring AG(2, p) and Full Proof of Erdős #617 (r^2) -/

def findSlopeAux (p dx dy : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => if (m * dx) % p == dy % p then m else findSlopeAux p dx dy m

def findSlope (p dx dy : Nat) : Nat := findSlopeAux p dx dy p

theorem findSlopeAux_lt {p dx dy n : Nat} (hp0 : 0 < p) (hn : n ≤ p) :
    findSlopeAux p dx dy n < p := by
  induction n with
  | zero => exact hp0
  | succ m ih =>
    unfold findSlopeAux
    by_cases h : ((m * dx) % p == dy % p) = true
    · simp only [h, ite_true]
      omega
    · simp only [h]
      exact ih (by omega)

theorem findSlopeAux_eq_of_mul_eq {p dx dy k n : Nat} (hp : IsPrime p)
    (hdx0 : 0 < dx) (hdxp : dx < p) (hk : k < n) (hnp : n ≤ p)
    (hmul : (k * dx) % p = dy % p) :
    findSlopeAux p dx dy n = k := by
  induction n with
  | zero => omega
  | succ m ih =>
    unfold findSlopeAux
    by_cases hmk : m = k
    · subst hmk
      have hcond : ((m * dx) % p == dy % p) = true := beq_iff_eq.mpr hmul
      simp only [hcond, ite_true]
    · have hcond : ((m * dx) % p == dy % p) = false := by
        apply beq_false_of_ne
        intro heq
        have heq' : (m * dx) % p = (k * dx) % p := heq.trans hmul.symm
        exact hmk (mod_mul_unique hp hdx0 hdxp (by omega) (by omega) heq')
      simp only [hcond]
      exact ih (by omega) (by omega)

theorem findSlope_eq_of_mul_eq {p dx dy k : Nat} (hp : IsPrime p)
    (hdx0 : 0 < dx) (hdxp : dx < p) (hk : k < p) (hmul : (k * dx) % p = dy % p) :
    findSlope p dx dy = k :=
  findSlopeAux_eq_of_mul_eq hp hdx0 hdxp hk (Nat.le_refl p) hmul

def affineColorVal (p : Nat) (u v : Fin p × Fin p) : Nat :=
  if u.1.val == v.1.val then 0
  else
    let dx := (v.1.val + p - u.1.val) % p
    let dy := (v.2.val + p - u.2.val) % p
    findSlope p dx dy

def affineColor (p : Nat) (hp0 : 0 < p) (u v : Fin p × Fin p) : Fin p :=
  ⟨affineColorVal p u v, by
    unfold affineColorVal
    by_cases h : (u.1.val == v.1.val) = true
    · simp only [h, ite_true]
      exact hp0
    · simp only [h]
      exact findSlopeAux_lt hp0 (Nat.le_refl p)⟩

theorem diff_mod_pos {p a b : Nat} (ha : a < p) (hb : b < p) (hne : a ≠ b) :
    0 < (b + p - a) % p ∧ (b + p - a) % p < p := by
  have hp0 : 0 < p := by omega
  refine ⟨?_, Nat.mod_lt _ hp0⟩
  by_cases hle : a ≤ b
  · have h1 : b + p - a = (b - a) + p := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · have h1 : b + p - a < p := by omega
    rw [Nat.mod_eq_of_lt h1]
    omega

theorem add_diff_mod {p a b : Nat} (ha : a < p) (hb : b < p) :
    (a + (b + p - a) % p) % p = b := by
  have h1 : (a + (b + p - a) % p) % p = (a + (b + p - a)) % p := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1]
  have h2 : a + (b + p - a) = b + p := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hb]

theorem diff_sum_mod_zero {p a b : Nat} (ha : a < p) (hb : b < p) :
    ((b + p - a) % p + (a + p - b) % p) % p = 0 := by
  have h1 : ((b + p - a) % p + (a + p - b) % p) % p = ((b + p - a) + (a + p - b)) % p := by
    rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1]
  have h2 : (b + p - a) + (a + p - b) = 2 * p := by omega
  rw [h2, Nat.mul_mod_left]

theorem affineColor_symm {p : Nat} (hp : IsPrime p) (hp0 : 0 < p) (u v : Fin p × Fin p) :
    affineColor p hp0 u v = affineColor p hp0 v u := by
  apply Fin.ext
  show affineColorVal p u v = affineColorVal p v u
  unfold affineColorVal
  by_cases heq : u.1.val = v.1.val
  · have h1 : (u.1.val == v.1.val) = true := beq_iff_eq.mpr heq
    have h2 : (v.1.val == u.1.val) = true := beq_iff_eq.mpr heq.symm
    simp only [h1, h2, ite_true]
  · have h1 : (u.1.val == v.1.val) = false := beq_false_of_ne heq
    have h2 : (v.1.val == u.1.val) = false := beq_false_of_ne (Ne.symm heq)
    simp only [h1, h2]
    let dx := (v.1.val + p - u.1.val) % p
    let dy := (v.2.val + p - u.2.val) % p
    let dx' := (u.1.val + p - v.1.val) % p
    let dy' := (u.2.val + p - v.2.val) % p
    have hdx := diff_mod_pos u.1.isLt v.1.isLt heq
    have hdx' := diff_mod_pos v.1.isLt u.1.isLt (Ne.symm heq)
    have hdy_lt : dy < p := Nat.mod_lt _ hp0
    rcases prime_mul_surjective hp hdx.1 hdx.2 hdy_lt with ⟨m, hm_lt, hm_eq⟩
    have hm_eq' : (m * dx) % p = dy % p := by rw [hm_eq, Nat.mod_eq_of_lt hdy_lt]
    have hfs1 : findSlope p dx dy = m := findSlope_eq_of_mul_eq hp hdx.1 hdx.2 hm_lt hm_eq'
    have hdx_sum : (dx + dx') % p = 0 := diff_sum_mod_zero u.1.isLt v.1.isLt
    have hdy_sum : (dy + dy') % p = 0 := diff_sum_mod_zero u.2.isLt v.2.isLt
    have hstep1 : (dy + m * dx') % p = (dy + dy') % p := by
      have hleft : (dy + m * dx') % p = (m * dx + m * dx') % p := by
        rw [Nat.add_mod, ← hm_eq, Nat.mod_mod, ← Nat.add_mod]
      rw [hleft, ← Nat.mul_add, Nat.mul_mod, hdx_sum, Nat.mul_zero, Nat.zero_mod, hdy_sum]
    have hm_eq2 : (m * dx') % p = dy' % p := mod_eq_of_add_mod_eq hp0 hstep1
    have hfs2 : findSlope p dx' dy' = m := findSlope_eq_of_mul_eq hp hdx'.1 hdx'.2 hm_lt hm_eq2
    exact hfs1.trans hfs2.symm

theorem affineColor_balanced {p : Nat} (hp : IsPrime p) (hp0 : 0 < p)
    (S : List (Fin p × Fin p)) (hpw : S.Pairwise (· ≠ ·)) (hlen : S.length = p + 1)
    (k : Fin p) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ affineColor p hp0 u v = k := by
  let proj : Fin p × Fin p → Nat := fun w => (w.2.val + (p - k.val) * w.1.val) % p
  have hlt : ∀ w ∈ S, proj w < p := fun w _ => Nat.mod_lt _ hp0
  have hlen' : p < S.length := by omega
  rcases list_pigeonhole p S proj hpw hlt hlen' with ⟨u, hu, v, hv, hne, hproj⟩
  refine ⟨u, hu, v, hv, hne, ?_⟩
  have hx_ne : u.1.val ≠ v.1.val := by
    intro hxeq
    have h1 : (u.2.val + (p - k.val) * u.1.val) % p = (v.2.val + (p - k.val) * u.1.val) % p := by
      simpa [proj, hxeq] using hproj
    rw [Nat.add_comm u.2.val, Nat.add_comm v.2.val] at h1
    have hy_mod : u.2.val % p = v.2.val % p := mod_eq_of_add_mod_eq hp0 h1
    rw [Nat.mod_eq_of_lt u.2.isLt, Nat.mod_eq_of_lt v.2.isLt] at hy_mod
    apply hne
    exact Prod.ext (Fin.ext hxeq) (Fin.ext hy_mod)
  apply Fin.ext
  show affineColorVal p u v = k.val
  unfold affineColorVal
  have hbf : (u.1.val == v.1.val) = false := beq_false_of_ne hx_ne
  simp only [hbf, Bool.false_eq_true, ite_false]
  let dx := (v.1.val + p - u.1.val) % p
  let dy := (v.2.val + p - u.2.val) % p
  have hdx := diff_mod_pos u.1.isLt v.1.isLt hx_ne
  have hv1 : (u.1.val + dx) % p = v.1.val := add_diff_mod u.1.isLt v.1.isLt
  have hv2 : (u.2.val + dy) % p = v.2.val := add_diff_mod u.2.isLt v.2.isLt
  have hsub : (u.2.val + (p - k.val) * u.1.val + (dy + (p - k.val) * dx)) % p =
      (v.2.val + (p - k.val) * v.1.val) % p := by
    have hrearr : u.2.val + (p - k.val) * u.1.val + (dy + (p - k.val) * dx) =
        (u.2.val + dy) + (p - k.val) * (u.1.val + dx) := by
      rw [Nat.mul_add]
      omega
    have hrhs : (v.2.val + (p - k.val) * v.1.val) % p =
        (v.2.val + (p - k.val) % p * v.1.val % p) % p := by
      rw [Nat.add_mod v.2.val, Nat.mod_eq_of_lt v.2.isLt,
          Nat.mul_mod (p - k.val) v.1.val, Nat.mod_eq_of_lt v.1.isLt]
    rw [hrearr, Nat.add_mod, hv2, Nat.mul_mod, hv1, hrhs]
  have hzero_eq : (u.2.val + (p - k.val) * u.1.val + (dy + (p - k.val) * dx)) % p =
      (u.2.val + (p - k.val) * u.1.val + 0) % p := by
    rw [Nat.add_zero]
    exact hsub.trans hproj.symm
  have hzero : (dy + (p - k.val) * dx) % p = 0 := by
    have h0 := mod_eq_of_add_mod_eq hp0 hzero_eq
    simpa using h0
  have hmul : (k.val * dx) % p = dy % p := by
    have hsum : (dy + (p - k.val) * dx + k.val * dx) % p = (k.val * dx) % p := by
      rw [Nat.add_mod, hzero, Nat.zero_add, Nat.mod_mod]
    have hcancel : dy + (p - k.val) * dx + k.val * dx = dy + p * dx := by
      have hkl : k.val ≤ p := Nat.le_of_lt k.isLt
      have hdist : (p - k.val) * dx + k.val * dx = p * dx := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hkl]
      omega
    rw [hcancel, Nat.add_mul_mod_self_left] at hsum
    exact hsum.symm
  exact findSlope_eq_of_mul_eq hp hdx.1 hdx.2 k.isLt hmul

/-- Main Theorem (`erdos_617.variants.r2`): For arbitrarily large r, K_{r^2} admits a symmetric
balanced r-coloring where every (r + 1)-subset contains edges of all r colors. -/
theorem erdos_617_variants_r2_infinite :
    ∀ N : Nat, ∃ p : Nat, N ≤ p ∧ IsPrime p ∧
      ∃ c : (Fin p × Fin p) → (Fin p × Fin p) → Fin p,
        (∀ u v, c u v = c v u) ∧
        (∀ (S : List (Fin p × Fin p)), S.Pairwise (· ≠ ·) → S.length = p + 1 →
          ∀ k : Fin p, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c u v = k) := by
  intro N
  rcases exists_prime_ge N with ⟨p, hNp, hp⟩
  have hp0 : 0 < p := by have := hp.1; omega
  exact ⟨p, hNp, hp, affineColor p hp0, affineColor_symm hp hp0, affineColor_balanced hp hp0⟩

end Erdos617R2
