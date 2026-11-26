module

@[expose] public section

/-
Standalone Lean 4 (v4.36.0) Formal Proof — Zero external imports, zero sorry, zero custom axioms.
Proves Erdős Problem #617 for r = 3 (`erdos_617.variants.r_eq_3`, Erdős–Gyárfás 1999):
Every symmetric 3-coloring of the complete graph K_10 contains a 4-vertex subset missing at least one color.
Proof structure (Single-Color Extremal Book Proof):
1. Pigeonhole on 90 directed edges of K_10 gives a color class G with sum of degrees <= 30 (|E(G)| <= 15).
2. In any balanced 3-coloring, every color class G has alpha(G) <= 3 and is diamond-free (no 4-set has >= 5 edges).
3. Any 10-vertex diamond-free graph with alpha(G) <= 3 has minimum degree delta <= 3; analyzing R = V \ N[v]
   rules out delta = 0 (sum >= 45), delta = 1 (sum >= 34), delta = 2 (sum >= 32 via diamond-free triangle bound),
   and delta = 3 (3-regular => 6 | 20 contradiction forces a triangle-free vertex v, whose R = K_3 + K_3 yields an
   independent 4-set {x, y, a, b}).
-/

namespace Erdos617R3

abbrev V := Fin 10

def all10 : List V := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

theorem all10_length : all10.length = 10 := rfl

theorem all10_nodup : all10.Pairwise (· ≠ ·) := by decide

theorem mem_all10 (v : V) : v ∈ all10 := by
  match v with
  | ⟨0, _⟩ => exact (by decide : (0 : V) ∈ all10)
  | ⟨1, _⟩ => exact (by decide : (1 : V) ∈ all10)
  | ⟨2, _⟩ => exact (by decide : (2 : V) ∈ all10)
  | ⟨3, _⟩ => exact (by decide : (3 : V) ∈ all10)
  | ⟨4, _⟩ => exact (by decide : (4 : V) ∈ all10)
  | ⟨5, _⟩ => exact (by decide : (5 : V) ∈ all10)
  | ⟨6, _⟩ => exact (by decide : (6 : V) ∈ all10)
  | ⟨7, _⟩ => exact (by decide : (7 : V) ∈ all10)
  | ⟨8, _⟩ => exact (by decide : (8 : V) ∈ all10)
  | ⟨9, _⟩ => exact (by decide : (9 : V) ∈ all10)

theorem filter_eq_singleton_all10 (v : V) :
    all10.filter (fun x => decide (x = v)) = [v] := by
  match v with
  | ⟨0, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (0 : V))) = [0])
  | ⟨1, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (1 : V))) = [1])
  | ⟨2, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (2 : V))) = [2])
  | ⟨3, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (3 : V))) = [3])
  | ⟨4, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (4 : V))) = [4])
  | ⟨5, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (5 : V))) = [5])
  | ⟨6, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (6 : V))) = [6])
  | ⟨7, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (7 : V))) = [7])
  | ⟨8, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (8 : V))) = [8])
  | ⟨9, _⟩ => exact (by decide : all10.filter (fun x => decide (x = (9 : V))) = [9])

theorem filter_ne_len_all10 (u : V) :
    (all10.filter (fun v => decide (u ≠ v))).length = 9 := by
  match u with
  | ⟨0, _⟩ => exact (by decide : (all10.filter (fun v => decide ((0 : V) ≠ v))).length = 9)
  | ⟨1, _⟩ => exact (by decide : (all10.filter (fun v => decide ((1 : V) ≠ v))).length = 9)
  | ⟨2, _⟩ => exact (by decide : (all10.filter (fun v => decide ((2 : V) ≠ v))).length = 9)
  | ⟨3, _⟩ => exact (by decide : (all10.filter (fun v => decide ((3 : V) ≠ v))).length = 9)
  | ⟨4, _⟩ => exact (by decide : (all10.filter (fun v => decide ((4 : V) ≠ v))).length = 9)
  | ⟨5, _⟩ => exact (by decide : (all10.filter (fun v => decide ((5 : V) ≠ v))).length = 9)
  | ⟨6, _⟩ => exact (by decide : (all10.filter (fun v => decide ((6 : V) ≠ v))).length = 9)
  | ⟨7, _⟩ => exact (by decide : (all10.filter (fun v => decide ((7 : V) ≠ v))).length = 9)
  | ⟨8, _⟩ => exact (by decide : (all10.filter (fun v => decide ((8 : V) ≠ v))).length = 9)
  | ⟨9, _⟩ => exact (by decide : (all10.filter (fun v => decide ((9 : V) ≠ v))).length = 9)

theorem eq_false_of_not_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> simp at h ⊢

/-! ### Part 1: List Counting and Double-Counting Lemmas -/

def degIn (adj : V → V → Bool) (S : List V) (u : V) : Nat :=
  (S.filter (fun v => adj u v)).length

def deg (adj : V → V → Bool) (u : V) : Nat :=
  degIn adj all10 u

def edgeSum (adj : V → V → Bool) : Nat :=
  (all10.map (deg adj)).sum

theorem list_sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem list_sum_map_le {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

theorem list_sum_const {α : Type} (l : List α) (c : Nat) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem filter_len_add_not {α : Type} (l : List α) (P : α → Bool) :
    (l.filter P).length + (l.filter (fun x => !P x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases h : P a <;>
      simp only [List.filter, h, Bool.not_true, Bool.not_false, List.length_cons] <;> omega

theorem filter_len_split {α : Type} (l : List α) (P Q : α → Bool) :
    (l.filter Q).length =
      ((l.filter P).filter Q).length + ((l.filter (fun x => !P x)).filter Q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hP : P a <;> cases hQ : Q a <;>
      simp only [List.filter, hP, hQ, Bool.not_true, Bool.not_false, List.length_cons] <;> omega

theorem sum_map_filter_add_not {α : Type} (l : List α) (P : α → Bool) (f : α → Nat) :
    ((l.filter P).map f).sum + ((l.filter (fun x => !P x)).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases h : P a <;>
      simp only [List.filter, h, Bool.not_true, Bool.not_false, List.map_cons, List.sum_cons] <;> omega

theorem double_count_edges (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (A B : List V) :
    (A.map (degIn adj B)).sum = (B.map (degIn adj A)).sum := by
  induction A with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have h0 : ∀ b ∈ B, degIn adj [] b = 0 := fun _ _ => rfl
    have hle := list_sum_map_le B (degIn adj []) (fun _ => 0) (fun b hb => Nat.le_of_eq (h0 b hb))
    rw [list_sum_const] at hle
    omega
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have hstep : ∀ b : V, degIn adj (a :: t) b = (if adj a b then 1 else 0) + degIn adj t b := by
      intro b
      unfold degIn
      simp only [List.filter]
      rw [hsymm b a]
      cases h : adj a b <;> simp only [List.length_cons, ite_true, Bool.false_eq_true, ite_false] <;> omega
    have hB : (B.map (degIn adj (a :: t))).sum =
        (B.map (fun b => if adj a b then 1 else 0)).sum + (B.map (degIn adj t)).sum := by
      rw [← list_sum_map_add]
      congr 1
      exact List.map_congr_left (fun b _ => hstep b)
    have hcount : ∀ L : List V, (L.map (fun b => if adj a b then 1 else 0)).sum = degIn adj L a := by
      intro L
      unfold degIn
      induction L with
      | nil => simp
      | cons b tb ihb =>
        cases h : adj a b
        · simp only [List.filter, List.map_cons, List.sum_cons, h, Bool.false_eq_true, ite_false]
          rw [ihb]; omega
        · simp only [List.filter, List.map_cons, List.sum_cons, List.length_cons, h, ite_true]
          rw [ihb]; omega
    rw [hB, hcount B, ih]

theorem all_eq_of_ge_and_sum_le {α : Type} (l : List α) (f : α → Nat) (c : Nat)
    (hge : ∀ x ∈ l, c ≤ f x) (hsum : (l.map f).sum ≤ l.length * c) :
    ∀ x ∈ l, f x = c := by
  induction l with
  | nil => intro x hx; cases hx
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have ht_ge : ∀ x ∈ t, c ≤ f x := fun x hx => hge x (List.mem_cons_of_mem a hx)
    have ht_sum : t.length * c ≤ (t.map f).sum := by
      rw [← list_sum_const t c]
      exact list_sum_map_le t (fun _ => c) f ht_ge
    have ha_ge : c ≤ f a := hge a List.mem_cons_self
    have hmul : (t.length + 1) * c = t.length * c + c := by rw [Nat.add_mul, Nat.one_mul]
    have ha_eq : f a = c := by omega
    have ht_le : (t.map f).sum ≤ t.length * c := by omega
    intro x hx
    cases hx with
    | head => exact ha_eq
    | tail _ hxt => exact ih ht_ge ht_le x hxt

theorem filter_len_eq_of_mem_unique {α : Type} [DecidableEq α] (l : List α) (u : α)
    (hpw : l.Pairwise (· ≠ ·)) (hu : u ∈ l) :
    (l.filter (fun x => decide (x = u))).length = 1 := by
  induction l with
  | nil => cases hu
  | cons a t ih =>
    have hpw' := List.pairwise_cons.mp hpw
    cases hu with
    | head =>
      have h0 : t.filter (fun x => decide (x = u)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simp only [decide_eq_true_eq]
        exact Ne.symm (hpw'.1 x hx)
      simp [List.filter, h0]
    | tail _ hut =>
      have hne : a ≠ u := hpw'.1 u hut
      have hd : decide (a = u) = false := decide_eq_false hne
      simp [List.filter, hd, ih hpw'.2 hut]

theorem exists_of_len_gt_sum {α : Type} (T : List α) (P Q : α → Bool)
    (hlen : (T.filter P).length + (T.filter Q).length < T.length) :
    ∃ t ∈ T, P t = false ∧ Q t = false := by
  induction T with
  | nil => simp at hlen
  | cons a rest ih =>
    cases hP : P a
    · cases hQ : Q a
      · exact ⟨a, List.mem_cons_self, hP, hQ⟩
      · simp only [List.filter, hP, hQ, List.length_cons] at hlen
        rcases ih (by omega) with ⟨t, ht, htP, htQ⟩
        exact ⟨t, List.mem_cons_of_mem a ht, htP, htQ⟩
    · cases hQ : Q a <;> simp only [List.filter, hP, hQ, List.length_cons] at hlen
      · rcases ih (by omega) with ⟨t, ht, htP, htQ⟩
        exact ⟨t, List.mem_cons_of_mem a ht, htP, htQ⟩
      · rcases ih (by omega) with ⟨t, ht, htP, htQ⟩
        exact ⟨t, List.mem_cons_of_mem a ht, htP, htQ⟩

theorem exists_two_of_len_ge_two {α : Type} (l : List α) (hpw : l.Pairwise (· ≠ ·))
    (hlen : 2 ≤ l.length) :
    ∃ a b : α, a ∈ l ∧ b ∈ l ∧ a ≠ b := by
  cases l with
  | nil => simp at hlen
  | cons a rest =>
    cases rest with
    | nil => simp at hlen
    | cons b t =>
      have hpw' := List.pairwise_cons.mp hpw
      exact ⟨a, b, List.mem_cons_self, List.mem_cons_of_mem a List.mem_cons_self,
        hpw'.1 b List.mem_cons_self⟩

/-! ### Part 2: Core Graph Predicates and Structural Lemmas -/

def AlphaLe3 (adj : V → V → Bool) : Prop :=
  ∀ a b d e : V,
    a ≠ b → a ≠ d → a ≠ e → b ≠ d → b ≠ e → d ≠ e →
    adj a b = true ∨ adj a d = true ∨ adj a e = true ∨
    adj b d = true ∨ adj b e = true ∨ adj d e = true

def DiamondFree (adj : V → V → Bool) : Prop :=
  ∀ a b d e : V,
    a ≠ b → a ≠ d → a ≠ e → b ≠ d → b ≠ e → d ≠ e →
    ¬(adj a b = true ∧ adj a d = true ∧ adj b d = true ∧ adj a e = true ∧ adj b e = true)

def AlphaLe2 (adj : V → V → Bool) (S : List V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ d ∈ S,
    a ≠ b → a ≠ d → b ≠ d →
    adj a b = true ∨ adj a d = true ∨ adj b d = true

def IsClique (adj : V → V → Bool) (S : List V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → adj a b = true

def nonNbrs (adj : V → V → Bool) (S : List V) (u : V) : List V :=
  S.filter (fun x => decide (x ≠ u) && !adj u x)

theorem nonNbrs_isClique (adj : V → V → Bool)
    (S : List V) (h2 : AlphaLe2 adj S) (u : V) (hu : u ∈ S) :
    IsClique adj (nonNbrs adj S u) := by
  intro a ha b hb hab
  have ha' := List.mem_filter.mp ha
  have hb' := List.mem_filter.mp hb
  have hau : a ≠ u := of_decide_eq_true (Bool.and_eq_true_iff.mp ha'.2).1
  have hbu : b ≠ u := of_decide_eq_true (Bool.and_eq_true_iff.mp hb'.2).1
  have hna : adj u a = false := eq_false_of_not_true (Bool.and_eq_true_iff.mp ha'.2).2
  have hnb : adj u b = false := eq_false_of_not_true (Bool.and_eq_true_iff.mp hb'.2).2
  rcases h2 u hu a ha'.1 b hb'.1 hau.symm hbu.symm hab with h | h | h
  · rw [hna] at h; cases h
  · rw [hnb] at h; cases h
  · exact h

theorem clique_len_le_three (adj : V → V → Bool) (hd : DiamondFree adj)
    (S : List V) (hpw : S.Pairwise (· ≠ ·)) (hc : IsClique adj S) :
    S.length ≤ 3 := by
  match S, hpw, hc with
  | [], _, _ => simp
  | [_], _, _ => simp
  | [_, _], _, _ => simp
  | [_, _, _], _, _ => simp
  | a :: b :: d :: e :: rest, hpw, hc =>
    exfalso
    have h1 := List.pairwise_cons.mp hpw
    have h2 := List.pairwise_cons.mp h1.2
    have h3 := List.pairwise_cons.mp h2.2
    have hab : a ≠ b := h1.1 b List.mem_cons_self
    have had : a ≠ d := h1.1 d (List.mem_cons_of_mem b List.mem_cons_self)
    have hae : a ≠ e := h1.1 e (List.mem_cons_of_mem b (List.mem_cons_of_mem d List.mem_cons_self))
    have hbd : b ≠ d := h2.1 d List.mem_cons_self
    have hbe : b ≠ e := h2.1 e (List.mem_cons_of_mem d List.mem_cons_self)
    have hde : d ≠ e := h3.1 e List.mem_cons_self
    have ma : a ∈ a :: b :: d :: e :: rest := List.mem_cons_self
    have mb : b ∈ a :: b :: d :: e :: rest := List.mem_cons_of_mem a List.mem_cons_self
    have md : d ∈ a :: b :: d :: e :: rest := List.mem_cons_of_mem a (List.mem_cons_of_mem b List.mem_cons_self)
    have me : e ∈ a :: b :: d :: e :: rest :=
      List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_of_mem d List.mem_cons_self))
    exact hd a b d e hab had hae hbd hbe hde
      ⟨hc a ma b mb hab, hc a ma d md had, hc b mb d md hbd, hc a ma e me hae, hc b mb e me hbe⟩

theorem split_vertex_list (adj : V → V → Bool) (hirr : ∀ u, adj u u = false)
    (S : List V) (hpw : S.Pairwise (· ≠ ·)) (u : V) (hu : u ∈ S) :
    S.length = 1 + degIn adj S u + (nonNbrs adj S u).length := by
  have h1 := filter_len_add_not S (fun x => decide (x = u))
  have hEq := filter_len_eq_of_mem_unique S u hpw hu
  let S' := S.filter (fun x => !decide (x = u))
  have h1' : (S.filter (fun x => decide (x = u))).length + S'.length = S.length := h1
  have h2 := filter_len_add_not S' (fun x => adj u x)
  have hdeg : (S'.filter (fun x => adj u x)).length = degIn adj S u := by
    unfold degIn
    have heq : S'.filter (fun x => adj u x) = S.filter (fun x => adj u x) := by
      dsimp [S']
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      by_cases hxu : x = u
      · subst hxu; simp [hirr x]
      · simp [hxu]
    rw [heq]
  have hnn : (S'.filter (fun x => !adj u x)).length = (nonNbrs adj S u).length := by
    unfold nonNbrs
    have heq : S'.filter (fun x => !adj u x) = S.filter (fun x => decide (x ≠ u) && !adj u x) := by
      dsimp [S']
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      by_cases hxu : x = u
      · subst hxu; simp
      · simp [hxu]
    rw [heq]
  omega

theorem degIn_ge_sub_four (adj : V → V → Bool)
    (hirr : ∀ u, adj u u = false) (hd : DiamondFree adj)
    (S : List V) (hpw : S.Pairwise (· ≠ ·)) (h2 : AlphaLe2 adj S) (u : V) (hu : u ∈ S) :
    S.length ≤ degIn adj S u + 4 := by
  have hsp := split_vertex_list adj hirr S hpw u hu
  have hcl := nonNbrs_isClique adj S h2 u hu
  have hpw_nn : (nonNbrs adj S u).Pairwise (· ≠ ·) := hpw.filter _
  have hle3 := clique_len_le_three adj hd (nonNbrs adj S u) hpw_nn hcl
  omega

/-- Diamond-free key bound: any vertex outside a triangle T has at most 1 neighbor in T. -/
theorem degIn_triangle_le_one (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (hd : DiamondFree adj) (T : List V) (hpw : T.Pairwise (· ≠ ·)) (hcl : IsClique adj T)
    (hlen : T.length = 3) (w : V) (hw : w ∉ T) :
    degIn adj T w ≤ 1 := by
  refine Classical.byContradiction (fun hgt => ?_)
  have hge2 : 2 ≤ (T.filter (fun t => adj w t)).length := by unfold degIn at hgt; omega
  have hpwF : (T.filter (fun t => adj w t)).Pairwise (· ≠ ·) := hpw.filter _
  rcases exists_two_of_len_ge_two _ hpwF hge2 with ⟨a, b, haF, hbF, hab⟩
  have haT : a ∈ T := (List.mem_filter.mp haF).1
  have hbT : b ∈ T := (List.mem_filter.mp hbF).1
  have hwa : adj w a = true := (List.mem_filter.mp haF).2
  have hwb : adj w b = true := (List.mem_filter.mp hbF).2
  have hex3 : ∃ c ∈ T, c ≠ a ∧ c ≠ b := by
    have hfa := filter_len_eq_of_mem_unique T a hpw haT
    have hfb := filter_len_eq_of_mem_unique T b hpw hbT
    have hlt : (T.filter (fun x => decide (x = a))).length +
        (T.filter (fun x => decide (x = b))).length < T.length := by omega
    rcases exists_of_len_gt_sum T (fun x => decide (x = a)) (fun x => decide (x = b)) hlt with
      ⟨c, hcT, hca, hcb⟩
    exact ⟨c, hcT, of_decide_eq_false hca, of_decide_eq_false hcb⟩
  rcases hex3 with ⟨c, hcT, hca, hcb⟩
  have hwa_ne : a ≠ w := fun h => hw (h ▸ haT)
  have hwb_ne : b ≠ w := fun h => hw (h ▸ hbT)
  have hwc_ne : c ≠ w := fun h => hw (h ▸ hcT)
  exact hd a b c w hab hca.symm hwa_ne hcb.symm hwb_ne hwc_ne
    ⟨hcl a haT b hbT hab, hcl a haT c hcT hca.symm, hcl b hbT c hcT hcb.symm,
     by rw [hsymm]; exact hwa, by rw [hsymm]; exact hwb⟩

/-- Two vertices outside a triangle T leave at least one vertex in T non-adjacent to both. -/
theorem exists_non_adj_both_of_triangle (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (hd : DiamondFree adj) (T : List V) (hpw : T.Pairwise (· ≠ ·)) (hcl : IsClique adj T)
    (hlen : T.length = 3) (x y : V) (hx : x ∉ T) (hy : y ∉ T) :
    ∃ t ∈ T, adj x t = false ∧ adj y t = false := by
  have hx1 := degIn_triangle_le_one adj hsymm hd T hpw hcl hlen x hx
  have hy1 := degIn_triangle_le_one adj hsymm hd T hpw hcl hlen y hy
  unfold degIn at hx1 hy1
  exact exists_of_len_gt_sum T (fun t => adj x t) (fun t => adj y t) (by omega)

theorem alphaLe2_of_nonNbrs (adj : V → V → Bool)
    (ha : AlphaLe3 adj) (v : V) :
    AlphaLe2 adj (nonNbrs adj all10 v) := by
  intro a haR b hbR d hdR hab had hbd
  have ha' := List.mem_filter.mp haR
  have hb' := List.mem_filter.mp hbR
  have hd' := List.mem_filter.mp hdR
  have hav : a ≠ v := of_decide_eq_true (Bool.and_eq_true_iff.mp ha'.2).1
  have hbv : b ≠ v := of_decide_eq_true (Bool.and_eq_true_iff.mp hb'.2).1
  have hdv : d ≠ v := of_decide_eq_true (Bool.and_eq_true_iff.mp hd'.2).1
  have hna : adj v a = false := eq_false_of_not_true (Bool.and_eq_true_iff.mp ha'.2).2
  have hnb : adj v b = false := eq_false_of_not_true (Bool.and_eq_true_iff.mp hb'.2).2
  have hnd : adj v d = false := eq_false_of_not_true (Bool.and_eq_true_iff.mp hd'.2).2
  rcases ha v a b d hav.symm hbv.symm hdv.symm hab had hbd with h | h | h | h | h | h
  · rw [hna] at h; cases h
  · rw [hnb] at h; cases h
  · rw [hnd] at h; cases h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ### Part 3: Ruling Out delta = 0, 1, 2 -/

theorem degIn_le_deg (adj : V → V → Bool) (P : V → Bool) (u : V) :
    degIn adj (all10.filter P) u ≤ deg adj u := by
  unfold deg degIn
  have hsp := filter_len_split all10 P (fun x => adj u x)
  omega

theorem edgeSum_split_R (adj : V → V → Bool) (hirr : ∀ u, adj u u = false) (v : V) :
    edgeSum adj =
      deg adj v +
      ((all10.filter (fun x => adj v x)).map (deg adj)).sum +
      ((nonNbrs adj all10 v).map (deg adj)).sum := by
  unfold edgeSum
  have h1 := sum_map_filter_add_not all10 (fun x => decide (x = v)) (deg adj)
  have hv_sum : ((all10.filter (fun x => decide (x = v))).map (deg adj)).sum = deg adj v := by
    rw [filter_eq_singleton_all10 v]; simp
  let S' := all10.filter (fun x => !decide (x = v))
  have h1' : ((all10.filter (fun x => decide (x = v))).map (deg adj)).sum + (S'.map (deg adj)).sum =
      (all10.map (deg adj)).sum := h1
  have h2 := sum_map_filter_add_not S' (fun x => adj v x) (deg adj)
  have hN : S'.filter (fun x => adj v x) = all10.filter (fun x => adj v x) := by
    dsimp [S']
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    by_cases hxv : x = v
    · subst hxv; simp [hirr x]
    · simp [hxv]
  have hR : S'.filter (fun x => !adj v x) = nonNbrs adj all10 v := by
    dsimp [S', nonNbrs]
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    by_cases hxv : x = v
    · subst hxv; simp
    · simp [hxv]
  rw [hN, hR] at h2
  omega

theorem deg_pos_of_nbr (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (v w : V) (hvw : adj v w = true) : 1 ≤ deg adj w := by
  unfold deg degIn
  have hv_mem : v ∈ all10.filter (fun x => adj w x) := by
    apply List.mem_filter.mpr
    exact ⟨mem_all10 v, by rw [hsymm]; exact hvw⟩
  cases hf : all10.filter (fun x => adj w x) with
  | nil => rw [hf] at hv_mem; cases hv_mem
  | cons _ _ => simp

/-- For delta = 2, every vertex u in R (|R| = 7) must have deg_R(u) >= 4. -/
theorem degIn_ge_four_of_len_seven (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (hirr : ∀ u, adj u u = false) (hd : DiamondFree adj)
    (R : List V) (hpw : R.Pairwise (· ≠ ·)) (h2 : AlphaLe2 adj R) (hlen : R.length = 7)
    (u : V) (hu : u ∈ R) :
    4 ≤ degIn adj R u := by
  have hge3 : 3 ≤ degIn adj R u := by
    have := degIn_ge_sub_four adj hirr hd R hpw h2 u hu
    omega
  refine Classical.byContradiction (fun hlt4 => ?_)
  have heq3 : degIn adj R u = 3 := by omega
  let T := nonNbrs adj R u
  let Nu := R.filter (fun x => adj u x)
  have hsp := split_vertex_list adj hirr R hpw u hu
  have hTlen : T.length = 3 := by dsimp [T]; unfold degIn at heq3; omega
  have hNlen : Nu.length = 3 := by dsimp [Nu]; exact heq3
  have hTcl : IsClique adj T := nonNbrs_isClique adj R h2 u hu
  have hTpw : T.Pairwise (· ≠ ·) := hpw.filter _
  have hNpw : Nu.Pairwise (· ≠ ·) := hpw.filter _
  have hnotT : ∀ w ∈ Nu, w ∉ T := by
    intro w hw hwT
    have h1 := (List.mem_filter.mp hw).2
    have h2' := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hwT).2).2
    rw [h1] at h2'; cases h2'
  have hNcl : IsClique adj Nu := by
    intro x hx y hy hxy
    rcases exists_non_adj_both_of_triangle adj hsymm hd T hTpw hTcl hTlen x y
      (hnotT x hx) (hnotT y hy) with ⟨t, htT, hxt, hyt⟩
    have hxR : x ∈ R := (List.mem_filter.mp hx).1
    have hyR : y ∈ R := (List.mem_filter.mp hy).1
    have htR : t ∈ R := (List.mem_filter.mp htT).1
    have htx : t ≠ x := fun h => hnotT x hx (h ▸ htT)
    have hty : t ≠ y := fun h => hnotT y hy (h ▸ htT)
    rcases h2 t htR x hxR y hyR htx hty hxy with h | h | h
    · rw [hsymm, hxt] at h; cases h
    · rw [hsymm, hyt] at h; cases h
    · exact h
  have hu_not_Nu : u ∉ Nu := by
    intro hmem
    have := (List.mem_filter.mp hmem).2
    rw [hirr u] at this; cases this
  have h4pw : (u :: Nu).Pairwise (· ≠ ·) := by
    apply List.pairwise_cons.mpr
    exact ⟨fun w hw heq => hu_not_Nu (heq ▸ hw), hNpw⟩
  have h4cl : IsClique adj (u :: Nu) := by
    intro a ha b hb hab
    cases ha with
    | head =>
      cases hb with
      | head => exact absurd rfl hab
      | tail _ hbN => exact (List.mem_filter.mp hbN).2
    | tail _ haN =>
      cases hb with
      | head => rw [hsymm]; exact (List.mem_filter.mp haN).2
      | tail _ hbN => exact hNcl a haN b hbN hab
  have hle3 := clique_len_le_three adj hd (u :: Nu) h4pw h4cl
  simp only [List.length_cons] at hle3
  omega

/-! ### Part 4: Ruling Out delta = 3 (3-Regular Diamond-Free Graph on 10 Vertices) -/

def orderedTriplesCountL (adj : V → V → Bool) (L : List V) : Nat :=
  (L.map (fun a =>
    (L.map (fun b =>
      (L.map (fun c =>
        if adj a b && adj b c && adj a c then 1 else 0)).sum)).sum)).sum

def unorderedTriplesCountL (adj : V → V → Bool) (L : List V) : Nat :=
  (L.map (fun a =>
    (L.map (fun b =>
      (L.map (fun c =>
        if decide (a.val < b.val) && decide (b.val < c.val) &&
           adj a b && adj b c && adj a c then 1 else 0)).sum)).sum)).sum

def orderedTriplesCount (adj : V → V → Bool) : Nat := orderedTriplesCountL adj all10
def unorderedTriplesCount (adj : V → V → Bool) : Nat := unorderedTriplesCountL adj all10

theorem six_orders_sum (x y z : Nat) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (if decide (x < y) && decide (y < z) then 1 else 0) +
    (if decide (x < z) && decide (z < y) then 1 else 0) +
    (if decide (y < x) && decide (x < z) then 1 else 0) +
    (if decide (y < z) && decide (z < x) then 1 else 0) +
    (if decide (z < x) && decide (x < y) then 1 else 0) +
    (if decide (z < y) && decide (y < x) then 1 else 0) = 1 := by
  by_cases h1 : x < y
  · by_cases h2 : y < z
    · have h3 : x < z := by omega
      have n1 : ¬(y < x) := by omega
      have n2 : ¬(z < y) := by omega
      have n3 : ¬(z < x) := by omega
      simp [h1, h2, h3, n1, n2, n3]
    · by_cases h3 : x < z
      · have hzy : z < y := by omega
        have n1 : ¬(y < x) := by omega
        have n3 : ¬(z < x) := by omega
        simp [h1, h2, h3, hzy, n1, n3]
      · have hzx : z < x := by omega
        have hzy : z < y := by omega
        have n1 : ¬(y < x) := by omega
        simp [h1, h2, h3, hzx, hzy, n1]
  · have hyx : y < x := by omega
    by_cases h2 : x < z
    · have hyz' : y < z := by omega
      have n2 : ¬(z < x) := by omega
      have n3 : ¬(z < y) := by omega
      simp [h1, hyx, h2, hyz', n2, n3]
    · have hzx : z < x := by omega
      by_cases h3 : y < z
      · have n3 : ¬(z < y) := by omega
        simp [h1, hyx, h2, hzx, h3, n3]
      · have hzy : z < y := by omega
        simp [h1, hyx, h2, hzx, h3, hzy]

theorem sum_comm_list (l1 l2 : List V) (G : V → V → Nat) :
    (l1.map (fun a => (l2.map (fun b => G a b)).sum)).sum =
    (l2.map (fun b => (l1.map (fun a => G a b)).sum)).sum := by
  induction l1 with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have h0 := list_sum_const l2 0
    omega
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← list_sum_map_add]

theorem orderedTriplesL_div_six (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (hirr : ∀ u, adj u u = false) (L : List V) :
    orderedTriplesCountL adj L = 6 * unorderedTriplesCountL adj L := by
  let sum3 (F : V → V → V → Nat) : Nat :=
    (L.map (fun a => (L.map (fun b => (L.map (fun c => F a b c)).sum)).sum)).sum
  have hswap12 : ∀ F : V → V → V → Nat, sum3 F = sum3 (fun a b c => F b a c) := fun F =>
    sum_comm_list L L (fun a b => (L.map (fun c => F a b c)).sum)
  have hswap23 : ∀ F : V → V → V → Nat, sum3 F = sum3 (fun a b c => F a c b) := by
    intro F
    dsimp [sum3]
    congr 1; apply List.map_congr_left; intro a _
    exact sum_comm_list L L (fun b c => F a b c)
  let T (a b c : V) : Bool := adj a b && adj b c && adj a c
  let I (a b c : V) : Nat :=
    if decide (a.val < b.val) && decide (b.val < c.val) && T a b c then 1 else 0
  have hTsym : ∀ a b c : V,
      T a b c = T b a c ∧ T a b c = T a c b ∧ T a b c = T b c a ∧
      T a b c = T c a b ∧ T a b c = T c b a := by
    intro a b c
    dsimp [T]
    rw [hsymm b a, hsymm c b, hsymm c a]
    cases adj a b <;> cases adj b c <;> cases adj a c <;> simp
  have hpoint : ∀ a b c : V,
      (if T a b c then 1 else 0) =
        I a b c + I a c b + I b a c + I b c a + I c a b + I c b a := by
    intro a b c
    by_cases hT : T a b c = true
    · have h12 : adj a b = true := by dsimp [T] at hT; revert hT; cases adj a b <;> simp
      have h23 : adj b c = true := by dsimp [T] at hT; revert hT; cases adj a b <;> cases adj b c <;> simp
      have h13 : adj a c = true := by dsimp [T] at hT; revert hT; cases adj a b <;> cases adj b c <;> cases adj a c <;> simp
      have hab : a.val ≠ b.val := by intro heq; have := Fin.ext heq; subst this; rw [hirr] at h12; cases h12
      have hbc : b.val ≠ c.val := by intro heq; have := Fin.ext heq; subst this; rw [hirr] at h23; cases h23
      have hac : a.val ≠ c.val := by intro heq; have := Fin.ext heq; subst this; rw [hirr] at h13; cases h13
      have hs := hTsym a b c
      dsimp [I]
      rw [hT, ← hs.1, ← hs.2.1, ← hs.2.2.1, ← hs.2.2.2.1, ← hs.2.2.2.2, hT]
      simp only [Bool.and_true, ite_true]
      exact (six_orders_sum a.val b.val c.val hab hbc hac).symm
    · have hTF : T a b c = false := Bool.eq_false_iff.mpr hT
      have hs := hTsym a b c
      dsimp [I]
      rw [hTF, ← hs.1, ← hs.2.1, ← hs.2.2.1, ← hs.2.2.2.1, ← hs.2.2.2.2, hTF]
      simp
  have hsum_add : ∀ F G : V → V → V → Nat, sum3 (fun a b c => F a b c + G a b c) = sum3 F + sum3 G := by
    intro F G
    dsimp [sum3]
    have step1 : ∀ a b : V,
        (L.map (fun c => F a b c + G a b c)).sum =
        (L.map (fun c => F a b c)).sum + (L.map (fun c => G a b c)).sum :=
      fun a b => list_sum_map_add L _ _
    have step2 : ∀ a : V,
        (L.map (fun b => (L.map (fun c => F a b c + G a b c)).sum)).sum =
        (L.map (fun b => (L.map (fun c => F a b c)).sum)).sum +
        (L.map (fun b => (L.map (fun c => G a b c)).sum)).sum := by
      intro a
      rw [← list_sum_map_add]
      congr 1; exact List.map_congr_left (fun b _ => step1 a b)
    rw [← list_sum_map_add]
    congr 1; exact List.map_congr_left (fun a _ => step2 a)
  have hS1 : sum3 (fun a b c => I a c b) = sum3 I := (hswap23 I).symm
  have hS2 : sum3 (fun a b c => I b a c) = sum3 I := (hswap12 I).symm
  have hS3 : sum3 (fun a b c => I b c a) = sum3 I := (hswap12 (fun a b c => I a c b)).symm.trans hS1
  have hS4 : sum3 (fun a b c => I c a b) = sum3 I := (hswap23 (fun a b c => I b a c)).symm.trans hS2
  have hS5 : sum3 (fun a b c => I c b a) = sum3 I := (hswap12 (fun a b c => I c a b)).symm.trans hS4
  have htot : orderedTriplesCountL adj L = sum3 (fun a b c => if T a b c then 1 else 0) := rfl
  have hun : unorderedTriplesCountL adj L = sum3 I := by
    unfold unorderedTriplesCountL
    dsimp [sum3, I, T]
    congr 1; apply List.map_congr_left; intro a _
    congr 1; apply List.map_congr_left; intro b _
    congr 1; apply List.map_congr_left; intro c _
    simp [Bool.and_assoc]
  rw [htot, hun]
  have hcongr : sum3 (fun a b c => if T a b c then 1 else 0) =
      sum3 (fun a b c => I a b c + I a c b + I b a c + I b c a + I c a b + I c b a) := by
    dsimp [sum3]
    congr 1; apply List.map_congr_left; intro a _
    congr 1; apply List.map_congr_left; intro b _
    congr 1; apply List.map_congr_left; intro c _
    exact hpoint a b c
  rw [hcongr, hsum_add, hsum_add, hsum_add, hsum_add, hsum_add, hS1, hS2, hS3, hS4, hS5]
  omega

theorem orderedTriples_div_six (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (hirr : ∀ u, adj u u = false) :
    orderedTriplesCount adj = 6 * unorderedTriplesCount adj :=
  orderedTriplesL_div_six adj hsymm hirr all10

/-- Local triangle count at vertex a equals sum_{b in N(a)} deg_{N(a)}(b). -/
theorem local_tri_eq (adj : V → V → Bool) (a : V) :
    (all10.map (fun b => (all10.map (fun c => if adj a b && adj b c && adj a c then 1 else 0)).sum)).sum =
    ((all10.filter (fun x => adj a x)).map (degIn adj (all10.filter (fun x => adj a x)))).sum := by
  let Na := all10.filter (fun x => adj a x)
  have hinner : ∀ b : V,
      (all10.map (fun c => if adj a b && adj b c && adj a c then 1 else 0)).sum =
      if adj a b then degIn adj Na b else 0 := by
    intro b
    cases hab : adj a b
    · simp only [Bool.false_and, Bool.false_eq_true, ite_false]
      have h0 := list_sum_const all10 0
      omega
    · simp only [Bool.true_and, ite_true]
      unfold degIn
      dsimp [Na]
      have hgen : ∀ l : List V,
          (l.map (fun c => if adj b c && adj a c then 1 else 0)).sum =
          ((l.filter (fun c => adj a c)).filter (fun c => adj b c)).length := by
        intro l
        induction l with
        | nil => simp
        | cons c t ih =>
          cases h1 : adj a c <;> cases h2 : adj b c <;>
            simp only [List.filter, List.map_cons, List.sum_cons, List.length_cons,
                       h1, h2, Bool.and_true, Bool.and_false, ite_true, Bool.false_eq_true, ite_false, ih] <;> omega
      exact hgen all10
  have hgen2 : ∀ l : List V,
      (l.map (fun b => if adj a b then degIn adj Na b else 0)).sum =
      ((l.filter (fun b => adj a b)).map (degIn adj Na)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons b t ih =>
      cases h : adj a b <;>
        simp only [List.filter, List.map_cons, List.sum_cons, h, ite_true, Bool.false_eq_true, ite_false, ih] <;> omega
  rw [show (all10.map (fun b => (all10.map (fun c => if adj a b && adj b c && adj a c then 1 else 0)).sum)).sum =
          (all10.map (fun b => if adj a b then degIn adj Na b else 0)).sum by
        congr 1; exact List.map_congr_left (fun b _ => hinner b)]
  exact hgen2 all10

/-- In a diamond-free graph, each vertex b in N(a) has at most 1 neighbor in N(a). -/
theorem degIn_nbr_le_one (adj : V → V → Bool) (hirr : ∀ u, adj u u = false)
    (hd : DiamondFree adj) (a b : V) (hab : adj a b = true) :
    degIn adj (all10.filter (fun x => adj a x)) b ≤ 1 := by
  refine Classical.byContradiction (fun hgt => ?_)
  let Na := all10.filter (fun x => adj a x)
  have hge2 : 2 ≤ (Na.filter (fun x => adj b x)).length := by dsimp [Na]; unfold degIn at hgt; omega
  have hpw : (Na.filter (fun x => adj b x)).Pairwise (· ≠ ·) := (all10_nodup.filter _).filter _
  rcases exists_two_of_len_ge_two _ hpw hge2 with ⟨d, e, hdF, heF, hde⟩
  have hdN : d ∈ Na := (List.mem_filter.mp hdF).1
  have heN : e ∈ Na := (List.mem_filter.mp heF).1
  have had : adj a d = true := (List.mem_filter.mp hdN).2
  have hae : adj a e = true := (List.mem_filter.mp heN).2
  have hbd : adj b d = true := (List.mem_filter.mp hdF).2
  have hbe : adj b e = true := (List.mem_filter.mp heF).2
  have hne_ab : a ≠ b := fun h => by subst h; rw [hirr] at hab; cases hab
  have hne_ad : a ≠ d := fun h => by subst h; rw [hirr] at had; cases had
  have hne_ae : a ≠ e := fun h => by subst h; rw [hirr] at hae; cases hae
  have hne_bd : b ≠ d := fun h => by subst h; rw [hirr] at hbd; cases hbd
  have hne_be : b ≠ e := fun h => by subst h; rw [hirr] at hbe; cases hbe
  exact hd a b d e hne_ab hne_ad hne_ae hne_bd hne_be hde ⟨hab, had, hbd, hae, hbe⟩

/-- For a vertex a of degree 3 in a diamond-free graph, local triangle sum is at most 2. -/
theorem local_tri_le_two (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (hirr : ∀ u, adj u u = false) (hd : DiamondFree adj) (a : V) (hdeg : deg adj a = 3) :
    ((all10.filter (fun x => adj a x)).map (degIn adj (all10.filter (fun x => adj a x)))).sum ≤ 2 := by
  have hlen : (all10.filter (fun x => adj a x)).length = 3 := hdeg
  match hNa : all10.filter (fun x => adj a x) with
  | [x, y, z] =>
    have hxN : x ∈ all10.filter (fun u => adj a u) := by rw [hNa]; exact List.mem_cons_self
    have hyN : y ∈ all10.filter (fun u => adj a u) := by rw [hNa]; exact List.mem_cons_of_mem x List.mem_cons_self
    have hzN : z ∈ all10.filter (fun u => adj a u) := by rw [hNa]; exact List.mem_cons_of_mem x (List.mem_cons_of_mem y List.mem_cons_self)
    have hax : adj a x = true := (List.mem_filter.mp hxN).2
    have hay : adj a y = true := (List.mem_filter.mp hyN).2
    have haz : adj a z = true := (List.mem_filter.mp hzN).2
    have dx : degIn adj [x, y, z] x ≤ 1 := by rw [← hNa]; exact degIn_nbr_le_one adj hirr hd a x hax
    have dy : degIn adj [x, y, z] y ≤ 1 := by rw [← hNa]; exact degIn_nbr_le_one adj hirr hd a y hay
    have dz : degIn adj [x, y, z] z ≤ 1 := by rw [← hNa]; exact degIn_nbr_le_one adj hirr hd a z haz
    have hsum_even : degIn adj [x, y, z] x + degIn adj [x, y, z] y + degIn adj [x, y, z] z =
        2 * ((if adj x y then 1 else 0) + (if adj x z then 1 else 0) + (if adj y z then 1 else 0)) := by
      unfold degIn
      simp only [List.filter, hirr, hsymm y x, hsymm z x, hsymm z y]
      cases adj x y <;> cases adj x z <;> cases adj y z <;> simp
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | [] => rw [hNa] at hlen; cases hlen
  | [_] => rw [hNa] at hlen; cases hlen
  | [_, _] => rw [hNa] at hlen; cases hlen
  | _ :: _ :: _ :: _ :: _ => rw [hNa] at hlen; simp at hlen

/-- In a 3-regular diamond-free graph on 10 vertices, some vertex has an independent neighborhood! -/
theorem exists_triangle_free_vertex (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (hirr : ∀ u, adj u u = false) (hd : DiamondFree adj) (hreg : ∀ v : V, deg adj v = 3) :
    ∃ v : V, ∀ x ∈ all10.filter (fun u => adj v u),
      ∀ y ∈ all10.filter (fun u => adj v u), adj x y = false := by
  refine Classical.byContradiction (fun hnone => ?_)
  have hall2 : ∀ v ∈ all10,
      (all10.map (fun b => (all10.map (fun c => if adj v b && adj b c && adj v c then 1 else 0)).sum)).sum = 2 := by
    intro v _
    rw [local_tri_eq]
    have hle2 := local_tri_le_two adj hsymm hirr hd v (hreg v)
    have hlen : (all10.filter (fun u => adj v u)).length = 3 := hreg v
    have hnotall : ¬(∀ x ∈ all10.filter (fun u => adj v u), ∀ y ∈ all10.filter (fun u => adj v u), adj x y = false) :=
      fun hall => hnone ⟨v, hall⟩
    match hNv : all10.filter (fun u => adj v u) with
    | [x, y, z] =>
      have hsum_even : degIn adj [x, y, z] x + degIn adj [x, y, z] y + degIn adj [x, y, z] z =
          2 * ((if adj x y then 1 else 0) + (if adj x z then 1 else 0) + (if adj y z then 1 else 0)) := by
        unfold degIn
        simp only [List.filter, hirr, hsymm y x, hsymm z x, hsymm z y]
        cases adj x y <;> cases adj x z <;> cases adj y z <;> simp
      have hpos : 0 < (if adj x y then 1 else 0) + (if adj x z then 1 else 0) + (if adj y z then 1 else 0) := by
        refine Classical.byContradiction (fun h0 => ?_)
        have hxy : adj x y = false := by cases h : adj x y <;> simp [h] at h0 ⊢
        have hxz : adj x z = false := by cases h : adj x z <;> simp [h] at h0 ⊢
        have hyz : adj y z = false := by cases h : adj y z <;> simp [h] at h0 ⊢
        apply hnotall
        rw [hNv]
        intro a ha b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact hirr _
        · exact hxy
        · exact hxz
        · rw [hsymm]; exact hxy
        · exact hirr _
        · exact hyz
        · rw [hsymm]; exact hxz
        · rw [hsymm]; exact hyz
        · exact hirr _
      rw [hNv] at hle2
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hle2 ⊢
      omega
    | [] => rw [hNv] at hlen; cases hlen
    | [_] => rw [hNv] at hlen; cases hlen
    | [_, _] => rw [hNv] at hlen; cases hlen
    | _ :: _ :: _ :: _ :: _ => rw [hNv] at hlen; simp at hlen
  have h20 : orderedTriplesCount adj = 20 := by
    unfold orderedTriplesCount orderedTriplesCountL
    have heq : (all10.map (fun a => (all10.map (fun b => (all10.map (fun c =>
        if adj a b && adj b c && adj a c then 1 else 0)).sum)).sum)) = all10.map (fun _ => 2) :=
      List.map_congr_left hall2
    rw [heq, list_sum_const, all10_length]
  have hdiv6 := orderedTriples_div_six adj hsymm hirr
  omega

/-- Case delta = 3 contradiction: 3-regular diamond-free graph on 10 vertices cannot have alpha <= 3. -/
theorem case_three_regular_false (adj : V → V → Bool) (hsymm : ∀ u v, adj u v = adj v u)
    (hirr : ∀ u, adj u u = false) (ha : AlphaLe3 adj) (hd : DiamondFree adj)
    (hreg : ∀ v : V, deg adj v = 3) : False := by
  rcases exists_triangle_free_vertex adj hsymm hirr hd hreg with ⟨v, hNv_ind⟩
  let N := all10.filter (fun x => adj v x)
  let R := nonNbrs adj all10 v
  have hNlen : N.length = 3 := hreg v
  have hsp := split_vertex_list adj hirr all10 all10_nodup v (mem_all10 v)
  have hRlen : R.length = 6 := by
    have hv3 : degIn adj all10 v = 3 := hreg v
    have h10 : all10.length = 10 := all10_length
    change all10.length = 1 + degIn adj all10 v + R.length at hsp
    omega
  have hRpw : R.Pairwise (· ≠ ·) := all10_nodup.filter _
  have hNpw : N.Pairwise (· ≠ ·) := all10_nodup.filter _
  have hR2 : AlphaLe2 adj R := alphaLe2_of_nonNbrs adj ha v
  have hdeg_split : ∀ u : V, deg adj u = (if adj u v then 1 else 0) + degIn adj N u + degIn adj R u := by
    intro u
    unfold deg degIn
    have h1 := filter_len_split all10 (fun x => decide (x = v)) (fun x => adj u x)
    have hv_part : ((all10.filter (fun x => decide (x = v))).filter (fun x => adj u x)).length =
        if adj u v then 1 else 0 := by
      rw [filter_eq_singleton_all10 v]
      cases h : adj u v <;> simp [List.filter, h]
    let S' := all10.filter (fun x => !decide (x = v))
    have h1' : (all10.filter (fun x => adj u x)).length =
        ((all10.filter (fun x => decide (x = v))).filter (fun x => adj u x)).length +
        (S'.filter (fun x => adj u x)).length := h1
    have h2 := filter_len_split S' (fun x => adj v x) (fun x => adj u x)
    have hN' : S'.filter (fun x => adj v x) = N := by
      dsimp [S', N]; rw [List.filter_filter]; apply List.filter_congr; intro x _
      by_cases hxv : x = v
      · subst hxv; simp [hirr x]
      · simp [hxv]
    have hR' : S'.filter (fun x => !adj v x) = R := by
      dsimp [S', R, nonNbrs]; rw [List.filter_filter]; apply List.filter_congr; intro x _
      by_cases hxv : x = v
      · subst hxv; simp
      · simp [hxv]
    rw [hN', hR'] at h2
    omega
  have hN_degR : ∀ w ∈ N, degIn adj R w = 2 := by
    intro w hw
    have hvw : adj v w = true := (List.mem_filter.mp hw).2
    have hwv : adj w v = true := by rw [hsymm]; exact hvw
    have hzero : degIn adj N w = 0 := by
      unfold degIn
      have hnil : N.filter (fun y => adj w y) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simp [hNv_ind w hw y hy]
      simp [hnil]
    have hds := hdeg_split w
    rw [hreg w, hwv, hzero] at hds
    simp at hds
    omega
  have hsum_RN : (R.map (degIn adj N)).sum = 6 := by
    rw [double_count_edges adj hsymm R N]
    have heq : N.map (degIn adj R) = N.map (fun _ => 2) := List.map_congr_left hN_degR
    rw [heq, list_sum_const, hNlen]
  have hR_split : ∀ u ∈ R, degIn adj R u + degIn adj N u = 3 := by
    intro u hu
    have hnv : adj v u = false := eq_false_of_not_true (Bool.and_eq_true_iff.mp (List.mem_filter.mp hu).2).2
    have huv : adj u v = false := by rw [hsymm]; exact hnv
    have hds := hdeg_split u
    rw [hreg u, huv] at hds
    simp at hds
    omega
  have hsum_RR : (R.map (degIn adj R)).sum = 12 := by
    have hadd : (R.map (fun u => degIn adj R u + degIn adj N u)).sum = 18 := by
      have heq : R.map (fun u => degIn adj R u + degIn adj N u) = R.map (fun _ => 3) :=
        List.map_congr_left hR_split
      rw [heq, list_sum_const, hRlen]
    rw [list_sum_map_add] at hadd
    omega
  have hR_ge2 : ∀ u ∈ R, 2 ≤ degIn adj R u := by
    intro u hu
    have := degIn_ge_sub_four adj hirr hd R hRpw hR2 u hu
    omega
  have hR_eq2 : ∀ u ∈ R, degIn adj R u = 2 :=
    all_eq_of_ge_and_sum_le R (degIn adj R) 2 hR_ge2 (by rw [hsum_RR, hRlen]; decide)
  have hex_a0 : ∃ a0, a0 ∈ R := by
    cases hR : R with
    | nil => rw [hR] at hRlen; cases hRlen
    | cons a0 _ => exact ⟨a0, List.mem_cons_self⟩
  rcases hex_a0 with ⟨a0, ha0R⟩
  let T2 := nonNbrs adj R a0
  let T1 := R.filter (fun u => decide (u = a0) || adj a0 u)
  have hsp_a0 := split_vertex_list adj hirr R hRpw a0 ha0R
  have hT2len : T2.length = 3 := by
    have := hR_eq2 a0 ha0R
    change R.length = 1 + degIn adj R a0 + T2.length at hsp_a0
    omega
  have hT2pw : T2.Pairwise (· ≠ ·) := hRpw.filter _
  have hT2cl : IsClique adj T2 := nonNbrs_isClique adj R hR2 a0 ha0R
  have hT1_compl : T1 = R.filter (fun u => !(decide (u ≠ a0) && !adj a0 u)) := by
    dsimp [T1]
    apply List.filter_congr
    intro u _
    by_cases hua : u = a0 <;> cases adj a0 u <;> simp [hua]
  have hT1len : T1.length = 3 := by
    have hf := filter_len_add_not R (fun u => decide (u ≠ a0) && !adj a0 u)
    rw [← hT1_compl] at hf
    change T2.length + T1.length = R.length at hf
    omega
  have hT1pw : T1.Pairwise (· ≠ ·) := hRpw.filter _
  have hno_cross : ∀ b ∈ T2, ∀ a ∈ T1, adj b a = false := by
    intro b hbT2 a haT1
    have hbR : b ∈ R := (List.mem_filter.mp hbT2).1
    have hdegT2 : degIn adj T2 b = 2 := by
      have hsp2 := split_vertex_list adj hirr T2 hT2pw b hbT2
      have hnn0 : (nonNbrs adj T2 b).length = 0 := by
        have hnil : nonNbrs adj T2 b = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro y hyT2
          by_cases hby : y = b
          · subst hby; simp
          · simp [hby, hT2cl b hbT2 y hyT2 (Ne.symm hby)]
        simp [hnil]
      omega
    have hsplitR := filter_len_split R (fun u => decide (u ≠ a0) && !adj a0 u) (fun u => adj b u)
    rw [← hT1_compl] at hsplitR
    change degIn adj R b = degIn adj T2 b + degIn adj T1 b at hsplitR
    have hdegT1_zero : degIn adj T1 b = 0 := by have := hR_eq2 b hbR; omega
    refine Classical.byContradiction (fun hba => ?_)
    have hbaT : adj b a = true := by cases h : adj b a <;> simp [h] at hba ⊢
    have ha_in : a ∈ T1.filter (fun u => adj b u) := List.mem_filter.mpr ⟨haT1, hbaT⟩
    cases hf : T1.filter (fun u => adj b u) with
    | nil => rw [hf] at ha_in; cases ha_in
    | cons _ _ => unfold degIn at hdegT1_zero; rw [hf] at hdegT1_zero; simp at hdegT1_zero
  have hT1cl : IsClique adj T1 := by
    intro a haT1 a' ha'T1 haa'
    have haR : a ∈ R := (List.mem_filter.mp haT1).1
    have hsplitR := filter_len_split R (fun u => decide (u ≠ a0) && !adj a0 u) (fun u => adj a u)
    rw [← hT1_compl] at hsplitR
    change degIn adj R a = degIn adj T2 a + degIn adj T1 a at hsplitR
    have hdegT2_zero : degIn adj T2 a = 0 := by
      unfold degIn
      have hnil : T2.filter (fun b => adj a b) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hbT2
        rw [hsymm, hno_cross b hbT2 a haT1]; simp
      simp [hnil]
    have hdegT1 : degIn adj T1 a = 2 := by have := hR_eq2 a haR; omega
    have hsp1 := split_vertex_list adj hirr T1 hT1pw a haT1
    have hnn0 : (nonNbrs adj T1 a).length = 0 := by omega
    refine Classical.byContradiction (fun hfalse => ?_)
    have hF : adj a a' = false := Bool.eq_false_iff.mpr hfalse
    have ha'_nn : a' ∈ nonNbrs adj T1 a := by
      apply List.mem_filter.mpr
      exact ⟨ha'T1, by simp [Ne.symm haa', hF]⟩
    cases hf : nonNbrs adj T1 a with
    | nil => rw [hf] at ha'_nn; cases ha'_nn
    | cons _ _ => rw [hf] at hnn0; simp at hnn0
  rcases exists_two_of_len_ge_two N hNpw (by omega) with ⟨x, y, hxN, hyN, hxy⟩
  have hx_not_R : x ∉ R := by
    intro hxR
    have h1 := (List.mem_filter.mp hxN).2
    have h2' := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hxR).2).2
    rw [h1] at h2'; cases h2'
  have hy_not_R : y ∉ R := by
    intro hyR
    have h1 := (List.mem_filter.mp hyN).2
    have h2' := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hyR).2).2
    rw [h1] at h2'; cases h2'
  have hx_not_T1 : x ∉ T1 := fun h => hx_not_R (List.mem_filter.mp h).1
  have hy_not_T1 : y ∉ T1 := fun h => hy_not_R (List.mem_filter.mp h).1
  have hx_not_T2 : x ∉ T2 := fun h => hx_not_R (List.mem_filter.mp h).1
  have hy_not_T2 : y ∉ T2 := fun h => hy_not_R (List.mem_filter.mp h).1
  rcases exists_non_adj_both_of_triangle adj hsymm hd T1 hT1pw hT1cl hT1len x y hx_not_T1 hy_not_T1 with
    ⟨a, haT1, hxa, hya⟩
  rcases exists_non_adj_both_of_triangle adj hsymm hd T2 hT2pw hT2cl hT2len x y hx_not_T2 hy_not_T2 with
    ⟨b, hbT2, hxb, hyb⟩
  have hxy_f : adj x y = false := hNv_ind x hxN y hyN
  have hab_f : adj a b = false := by rw [hsymm]; exact hno_cross b hbT2 a haT1
  have hax_ne : x ≠ a := fun h => hx_not_T1 (h ▸ haT1)
  have hbx_ne : x ≠ b := fun h => hx_not_T2 (h ▸ hbT2)
  have hay_ne : y ≠ a := fun h => hy_not_T1 (h ▸ haT1)
  have hby_ne : y ≠ b := fun h => hy_not_T2 (h ▸ hbT2)
  have hab_ne : a ≠ b := by
    intro heq
    subst heq
    have h1 := (List.mem_filter.mp haT1).2
    have h2' := (List.mem_filter.mp hbT2).2
    by_cases haa0 : a = a0
    · subst haa0; simp at h2'
    · simp [haa0] at h1 h2'
      rw [h1] at h2'; cases h2'
  rcases ha x y a b hxy hax_ne hbx_ne hay_ne hby_ne hab_ne with h | h | h | h | h | h
  · rw [hxy_f] at h; cases h
  · rw [hxa] at h; cases h
  · rw [hxb] at h; cases h
  · rw [hya] at h; cases h
  · rw [hyb] at h; cases h
  · rw [hab_f] at h; cases h

/-! ### Part 5: Single-Color Extremal Theorem and Main Theorem `erdos_617.variants.r_eq_3` -/

theorem diamond_free_alpha3_edgeSum_gt_30 (adj : V → V → Bool)
    (hsymm : ∀ u v, adj u v = adj v u) (hirr : ∀ u, adj u u = false)
    (ha : AlphaLe3 adj) (hd : DiamondFree adj) (hsum : edgeSum adj ≤ 30) : False := by
  by_cases hge3 : ∀ v : V, 3 ≤ deg adj v
  · have hreg : ∀ v : V, deg adj v = 3 := fun v =>
      all_eq_of_ge_and_sum_le all10 (deg adj) 3 (fun u _ => hge3 u)
        (by rw [all10_length]; exact hsum) v (mem_all10 v)
    exact case_three_regular_false adj hsymm hirr ha hd hreg
  · have hex_le2 : ∃ v : V, deg adj v ≤ 2 := by
      refine Classical.byContradiction (fun hno => ?_)
      apply hge3
      intro v
      refine Classical.byContradiction (fun hlt3 => ?_)
      exact hno ⟨v, by omega⟩
    rcases hex_le2 with ⟨v, hdv⟩
    let R := nonNbrs adj all10 v
    let N := all10.filter (fun x => adj v x)
    have hsp := split_vertex_list adj hirr all10 all10_nodup v (mem_all10 v)
    have hRlen : R.length = 9 - deg adj v := by
      have h10 : all10.length = 10 := all10_length
      change all10.length = 1 + deg adj v + R.length at hsp
      omega
    have hRpw : R.Pairwise (· ≠ ·) := all10_nodup.filter _
    have hR2 : AlphaLe2 adj R := alphaLe2_of_nonNbrs adj ha v
    have hes : edgeSum adj = deg adj v + (N.map (deg adj)).sum + (R.map (deg adj)).sum :=
      edgeSum_split_R adj hirr v
    have hN_ge : deg adj v ≤ (N.map (deg adj)).sum := by
      have hle : N.length * 1 ≤ (N.map (deg adj)).sum := by
        rw [← list_sum_const N 1]
        exact list_sum_map_le N (fun _ => 1) (deg adj)
          (fun w hw => deg_pos_of_nbr adj hsymm v w (List.mem_filter.mp hw).2)
      have hNlen : N.length = deg adj v := rfl
      omega
    have hR_le_deg : ∀ u ∈ R, degIn adj R u ≤ deg adj u := fun u _ =>
      degIn_le_deg adj (fun x => decide (x ≠ v) && !adj v x) u
    have hR_sum_le : (R.map (degIn adj R)).sum ≤ (R.map (deg adj)).sum :=
      list_sum_map_le R (degIn adj R) (deg adj) hR_le_deg
    match hdv_eq : deg adj v with
    | 0 =>
      have hR9 : R.length = 9 := by omega
      have hge45 : 45 ≤ (R.map (degIn adj R)).sum := by
        have h1 := list_sum_map_le R (fun _ => 5) (degIn adj R) (fun u hu => by
          have := degIn_ge_sub_four adj hirr hd R hRpw hR2 u hu; omega)
        rw [list_sum_const, hR9] at h1
        omega
      omega
    | 1 =>
      have hR8 : R.length = 8 := by omega
      have hge32 : 32 ≤ (R.map (degIn adj R)).sum := by
        have h1 := list_sum_map_le R (fun _ => 4) (degIn adj R) (fun u hu => by
          have := degIn_ge_sub_four adj hirr hd R hRpw hR2 u hu; omega)
        rw [list_sum_const, hR8] at h1
        omega
      omega
    | 2 =>
      have hR7 : R.length = 7 := by omega
      have hge28 : 28 ≤ (R.map (degIn adj R)).sum := by
        have h1 := list_sum_map_le R (fun _ => 4) (degIn adj R)
          (fun u hu => degIn_ge_four_of_len_seven adj hsymm hirr hd R hRpw hR2 hR7 u hu)
        rw [list_sum_const, hR7] at h1
        omega
      omega
    | _ + 3 => omega

def colorAdj (c : V → V → Fin 3) (k : Fin 3) (u v : V) : Bool :=
  decide (u ≠ v) && decide (c u v = k)

theorem colorAdj_symm (c : V → V → Fin 3) (hsymm : ∀ u v, c u v = c v u) (k : Fin 3) :
    ∀ u v, colorAdj c k u v = colorAdj c k v u := by
  intro u v
  unfold colorAdj
  rw [hsymm v u]
  by_cases huv : u = v
  · subst huv; simp
  · simp [huv, Ne.symm huv]

theorem colorAdj_irr (c : V → V → Fin 3) (k : Fin 3) : ∀ u, colorAdj c k u u = false := by
  intro u; simp [colorAdj]

theorem colorAdj_sum_90 (c : V → V → Fin 3) :
    edgeSum (colorAdj c 0) + edgeSum (colorAdj c 1) + edgeSum (colorAdj c 2) = 90 := by
  have hdeg9 : ∀ u : V,
      deg (colorAdj c 0) u + deg (colorAdj c 1) u + deg (colorAdj c 2) u = 9 := by
    intro u
    unfold deg degIn
    have hgen : ∀ l : List V,
        (l.filter (colorAdj c 0 u)).length + (l.filter (colorAdj c 1 u)).length +
        (l.filter (colorAdj c 2 u)).length = (l.filter (fun v => decide (u ≠ v))).length := by
      intro l
      induction l with
      | nil => simp
      | cons v t ih =>
        by_cases huv : u = v
        · subst huv
          have hdF : decide (u ≠ u) = false := decide_eq_false (fun h => h rfl)
          simp only [List.filter, colorAdj, hdF, Bool.false_and, ih]
        · have hdT : decide (u ≠ v) = true := decide_eq_true huv
          have hc : c u v = 0 ∨ c u v = 1 ∨ c u v = 2 := by
            match c u v with
            | ⟨0, _⟩ => exact Or.inl rfl
            | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
            | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)
          rcases hc with h | h | h
          · have h0 : decide (c u v = (0 : Fin 3)) = true := decide_eq_true h
            have h1 : decide (c u v = (1 : Fin 3)) = false := by rw [h]; decide
            have h2 : decide (c u v = (2 : Fin 3)) = false := by rw [h]; decide
            simp only [List.filter, colorAdj, hdT, h0, h1, h2, Bool.true_and, List.length_cons]
            omega
          · have h0 : decide (c u v = (0 : Fin 3)) = false := by rw [h]; decide
            have h1 : decide (c u v = (1 : Fin 3)) = true := decide_eq_true h
            have h2 : decide (c u v = (2 : Fin 3)) = false := by rw [h]; decide
            simp only [List.filter, colorAdj, hdT, h0, h1, h2, Bool.true_and, List.length_cons]
            omega
          · have h0 : decide (c u v = (0 : Fin 3)) = false := by rw [h]; decide
            have h1 : decide (c u v = (1 : Fin 3)) = false := by rw [h]; decide
            have h2 : decide (c u v = (2 : Fin 3)) = true := decide_eq_true h
            simp only [List.filter, colorAdj, hdT, h0, h1, h2, Bool.true_and, List.length_cons]
            omega
    rw [hgen, filter_ne_len_all10 u]
  unfold edgeSum
  rw [← list_sum_map_add, ← list_sum_map_add]
  have heq : all10.map (fun u => deg (colorAdj c 0) u + deg (colorAdj c 1) u + deg (colorAdj c 2) u) =
      all10.map (fun _ => 9) := List.map_congr_left (fun u _ => hdeg9 u)
  rw [heq, list_sum_const, all10_length]

/-- Main Theorem (`erdos_617.variants.r_eq_3`): Every symmetric 3-coloring of K_10 has a 4-vertex
subset missing at least one color. -/
theorem erdos_617_variants_r_eq_3 (c : V → V → Fin 3) (hsymm : ∀ u v, c u v = c v u) :
    ∃ (a b d e : V) (k : Fin 3),
      a ≠ b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e ∧
      c a b ≠ k ∧ c a d ≠ k ∧ c a e ≠ k ∧ c b d ≠ k ∧ c b e ≠ k ∧ c d e ≠ k := by
  refine Classical.byContradiction (fun hbal => ?_)
  have h_alpha : ∀ k : Fin 3, AlphaLe3 (colorAdj c k) := by
    intro k a b d e hab had hae hbd hbe hde
    refine Classical.byContradiction (fun hno => ?_)
    apply hbal
    refine ⟨a, b, d, e, k, hab, had, hae, hbd, hbe, hde, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; apply hno; left; simp [colorAdj, hab, h]
    · intro h; apply hno; right; left; simp [colorAdj, had, h]
    · intro h; apply hno; right; right; left; simp [colorAdj, hae, h]
    · intro h; apply hno; right; right; right; left; simp [colorAdj, hbd, h]
    · intro h; apply hno; right; right; right; right; left; simp [colorAdj, hbe, h]
    · intro h; apply hno; right; right; right; right; right; simp [colorAdj, hde, h]
  have h_diam : ∀ k : Fin 3, DiamondFree (colorAdj c k) := by
    intro k a b d e hab had hae hbd hbe hde ⟨h1, h2, h3, h4, h5⟩
    have hc1 : c a b = k := of_decide_eq_true (Bool.and_eq_true_iff.mp h1).2
    have hc2 : c a d = k := of_decide_eq_true (Bool.and_eq_true_iff.mp h2).2
    have hc3 : c b d = k := of_decide_eq_true (Bool.and_eq_true_iff.mp h3).2
    have hc4 : c a e = k := of_decide_eq_true (Bool.and_eq_true_iff.mp h4).2
    have hc5 : c b e = k := of_decide_eq_true (Bool.and_eq_true_iff.mp h5).2
    have hex_k' : ∃ k' : Fin 3, k' ≠ k ∧ k' ≠ c d e := by
      have hk012 : k = 0 ∨ k = 1 ∨ k = 2 := by
        match k with | ⟨0, _⟩ => exact Or.inl rfl | ⟨1, _⟩ => exact Or.inr (Or.inl rfl) | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)
      have hc012 : c d e = 0 ∨ c d e = 1 ∨ c d e = 2 := by
        match c d e with | ⟨0, _⟩ => exact Or.inl rfl | ⟨1, _⟩ => exact Or.inr (Or.inl rfl) | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)
      rcases hk012 with rfl | rfl | rfl <;> rcases hc012 with h | h | h <;> rw [h]
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
    rcases hex_k' with ⟨k', hk1, hk2⟩
    exact hbal ⟨a, b, d, e, k', hab, had, hae, hbd, hbe, hde,
      hc1 ▸ hk1.symm, hc2 ▸ hk1.symm, hc4 ▸ hk1.symm, hc3 ▸ hk1.symm, hc5 ▸ hk1.symm, hk2.symm⟩
  have hsum90 := colorAdj_sum_90 c
  have hex_le30 : ∃ k : Fin 3, edgeSum (colorAdj c k) ≤ 30 := by
    by_cases h0 : edgeSum (colorAdj c 0) ≤ 30
    · exact ⟨0, h0⟩
    · by_cases h1 : edgeSum (colorAdj c 1) ≤ 30
      · exact ⟨1, h1⟩
      · exact ⟨2, by omega⟩
  rcases hex_le30 with ⟨k, hk30⟩
  exact diamond_free_alpha3_edgeSum_gt_30 (colorAdj c k)
    (colorAdj_symm c hsymm k) (colorAdj_irr c k) (h_alpha k) (h_diam k) hk30

end Erdos617R3
