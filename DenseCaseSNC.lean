import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith

/-!
# A dense case of Seymour's second-neighborhood conjecture

This file formalizes the fixed-target counting proof in `dense-case-snc.tex`.
-/

open Finset

namespace DenseCaseSNC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite oriented graph, represented by its arc relation. -/
structure OrientedGraph (V : Type*) [Fintype V] [DecidableEq V] where
  Arc : V → V → Prop
  decArc : DecidableRel Arc
  loopless : ∀ v, ¬ Arc v v
  asymmetric : ∀ ⦃u v⦄, Arc u v → ¬ Arc v u

attribute [instance] OrientedGraph.decArc

namespace OrientedGraph

variable (G : OrientedGraph V)

def outNeighbors (v : V) : Finset V := univ.filter (G.Arc v)

def inNeighbors (v : V) : Finset V := univ.filter (fun u => G.Arc u v)

def secondNeighbors (v : V) : Finset V :=
  univ.filter fun x => ¬ G.Arc v x ∧ ∃ y, G.Arc v y ∧ G.Arc y x

def unreachable (v : V) : Finset V :=
  univ.filter fun x => x ≠ v ∧ ¬ G.Arc v x ∧ ¬ ∃ y, G.Arc v y ∧ G.Arc y x

def trap (x : V) : Finset V :=
  univ.filter fun y => y ≠ x ∧ ¬ G.Arc y x

def predecessors (x : V) : Finset V :=
  univ.filter fun v => x ∈ G.unreachable v

def outDegree (v : V) : ℕ := (G.outNeighbors v).card

def inDegree (v : V) : ℕ := (G.inNeighbors v).card

def IsSeymour (v : V) : Prop := G.outDegree v ≤ (G.secondNeighbors v).card

@[simp] theorem mem_outNeighbors {v x : V} : x ∈ G.outNeighbors v ↔ G.Arc v x := by
  simp [outNeighbors]

@[simp] theorem mem_inNeighbors {v x : V} : x ∈ G.inNeighbors v ↔ G.Arc x v := by
  simp [inNeighbors]

@[simp] theorem mem_secondNeighbors {v x : V} :
    x ∈ G.secondNeighbors v ↔ ¬ G.Arc v x ∧ ∃ y, G.Arc v y ∧ G.Arc y x := by
  simp [secondNeighbors]

@[simp] theorem mem_unreachable {v x : V} :
    x ∈ G.unreachable v ↔
      x ≠ v ∧ ¬ G.Arc v x ∧ ¬ ∃ y, G.Arc v y ∧ G.Arc y x := by
  simp [unreachable]

@[simp] theorem mem_trap {x y : V} : y ∈ G.trap x ↔ y ≠ x ∧ ¬ G.Arc y x := by
  simp [trap]

@[simp] theorem mem_predecessors {v x : V} :
    v ∈ G.predecessors x ↔ x ∈ G.unreachable v := by
  simp [predecessors]

/-- An oriented graph has at most `choose |S| 2` arcs internal to a vertex set `S`. -/
theorem internal_arcs_le_choose (S : Finset V) :
    ((S.offDiag).filter fun e : V × V => G.Arc e.1 e.2).card ≤ S.card.choose 2 := by
  let A := (S.offDiag).filter fun e : V × V => G.Arc e.1 e.2
  have hinj : Set.InjOn Sym2.mk (A : Set (V × V)) := by
    intro a ha b hb hab
    rcases (Sym2.mk_eq_mk_iff.mp hab) with hab | hab
    · exact hab
    · exfalso
      have harca : G.Arc a.1 a.2 := (by simpa [A] using ha : _ ∧ G.Arc a.1 a.2).2
      have harcb : G.Arc b.1 b.2 := (by simpa [A] using hb : _ ∧ G.Arc b.1 b.2).2
      have hswap : a.1 = b.2 ∧ a.2 = b.1 := by
        simpa [Prod.ext_iff] using congrArg (fun z : V × V => (z.1, z.2)) hab
      exact (G.asymmetric harca) (hswap.2 ▸ hswap.1 ▸ harcb)
  calc
    A.card = (A.image Sym2.mk).card := (card_image_of_injOn hinj).symm
    _ ≤ (S.offDiag.image Sym2.mk).card :=
      card_le_card (Finset.image_mono Sym2.mk (filter_subset _ _))
    _ = S.card.choose 2 := Sym2.card_image_offDiag S

/-- The algebraic rearrangement used at the end of the capacity count. -/
private theorem capacity_arithmetic {δ p t q : ℕ} (hp : 0 < p) (hpt : p ≤ t)
    (ht : t = δ + q) (hcount : δ * p ≤ p.choose 2 + p * (t - p)) :
    p + 1 ≤ 2 * q := by
  have hcountQ : ((δ * p : ℕ) : ℚ) ≤ ((p.choose 2 + p * (t - p) : ℕ) : ℚ) :=
    Nat.cast_le.mpr hcount
  simp only [Nat.cast_add, Nat.cast_mul] at hcountQ
  rw [Nat.cast_choose_two ℚ p, Nat.cast_sub hpt] at hcountQ
  have htQ : (t : ℚ) = δ + q := by
    simpa only [Nat.cast_add] using congrArg (fun z : ℕ => (z : ℚ)) ht
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hresultQ : (p : ℚ) + 1 ≤ 2 * q := by nlinarith
  exact_mod_cast hresultQ

private theorem sum_internal_arcs_le_choose (S : Finset V) :
    (∑ y ∈ S, #(S.bipartiteBelow G.Arc y)) ≤ S.card.choose 2 := by
  have hoff :
      (S.offDiag.filter fun e : V × V => G.Arc e.1 e.2) =
        ((S ×ˢ S).filter fun e : V × V => G.Arc e.1 e.2) := by
    ext e
    rcases e with ⟨u, v⟩
    simp only [mem_filter, mem_offDiag, mem_product, Prod.fst, Prod.snd]
    constructor
    · rintro ⟨⟨hu, hv, _⟩, huv⟩
      exact ⟨⟨hu, hv⟩, huv⟩
    · rintro ⟨⟨hu, hv⟩, huv⟩
      exact ⟨⟨hu, hv, fun h => G.loopless v (h ▸ huv)⟩, huv⟩
  have hcard :
      ((S ×ˢ S).filter fun e : V × V => G.Arc e.1 e.2).card =
        ∑ y ∈ S, #(S.bipartiteBelow G.Arc y) := by
    simp only [card_eq_sum_ones, sum_filter, sum_product, bipartiteBelow]
    rw [sum_comm]
  rw [← hcard, ← hoff]
  exact G.internal_arcs_le_choose S

/-- The fixed-target capacity lemma from the paper, in subtraction-free form.
If some source cannot reach `x` within two steps, then
`|P(x)| + 1 ≤ 2 (|T(x)| - δ)`. -/
theorem fixed_target_capacity (δ : ℕ) (hmin : ∀ v, δ ≤ G.outDegree v) (x : V)
    (hP : (G.predecessors x).Nonempty) :
    (G.predecessors x).card + 1 ≤ 2 * ((G.trap x).card - δ) := by
  let P := G.predecessors x
  let T := G.trap x
  let p := P.card
  let t := T.card
  let q := t - δ
  have hPT : P ⊆ T := by
    intro v hv
    have huv : x ∈ G.unreachable v := by simpa [P] using hv
    exact G.mem_trap.mpr
      ⟨(G.mem_unreachable.mp huv).1.symm, (G.mem_unreachable.mp huv).2.1⟩
  have houtT : ∀ v ∈ P, G.outNeighbors v ⊆ T := by
    intro v hv y hy
    have huv : x ∈ G.unreachable v := by simpa [P] using hv
    have hxy := G.mem_unreachable.mp huv
    have hvy : G.Arc v y := G.mem_outNeighbors.mp hy
    apply G.mem_trap.mpr
    constructor
    · intro hyx
      exact hxy.2.1 (hyx ▸ hvy)
    · intro hyx
      exact hxy.2.2 ⟨y, hvy, hyx⟩
  have hδt : δ ≤ t := by
    obtain ⟨v, hv⟩ := hP
    calc
      δ ≤ G.outDegree v := hmin v
      _ ≤ t := card_le_card (houtT v (by simpa [P] using hv))
  have hpt : p ≤ t := card_le_card hPT
  have htq : t = δ + q := by
    dsimp [q]
    omega
  have hp : 0 < p := by simpa [p, P, card_pos] using hP
  have hfiber : ∀ v ∈ P,
      #(T.bipartiteAbove G.Arc v) = G.outDegree v := by
    intro v hv
    apply congrArg card
    ext y
    simp only [mem_bipartiteAbove, G.mem_outNeighbors]
    exact and_iff_right_iff_imp.mpr fun hy => houtT v hv (G.mem_outNeighbors.mpr hy)
  have hlower : p * δ ≤ ∑ v ∈ P, #(T.bipartiteAbove G.Arc v) := by
    simpa [p, nsmul_eq_mul] using
      P.card_nsmul_le_sum (fun v => #(T.bipartiteAbove G.Arc v)) δ
        (fun v hv => by
          change δ ≤ #(T.bipartiteAbove G.Arc v)
          rw [hfiber v hv]
          exact hmin v)
  have hdouble :
      (∑ v ∈ P, #(T.bipartiteAbove G.Arc v)) =
        ∑ y ∈ T, #(P.bipartiteBelow G.Arc y) :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Arc
  have hfilter : T.filter (fun y => y ∈ P) = P := by
    ext y
    simp only [mem_filter]
    constructor
    · exact fun h => h.2
    · exact fun hy => ⟨hPT hy, hy⟩
  have hfilterNot : T.filter (fun y => y ∉ P) = T \ P := by
    ext y
    simp
  have hexternal :
      (∑ y ∈ T \ P, #(P.bipartiteBelow G.Arc y)) ≤ (t - p) * p := by
    have h := (T \ P).sum_le_card_nsmul
      (fun y => #(P.bipartiteBelow G.Arc y)) p
      (fun y _ => card_le_card (filter_subset _ _))
    simpa [t, p, card_sdiff hPT, nsmul_eq_mul, Nat.mul_comm] using h
  have hupper :
      (∑ y ∈ T, #(P.bipartiteBelow G.Arc y)) ≤ p.choose 2 + p * (t - p) := by
    rw [← sum_filter_add_sum_filter_not T (fun y => y ∈ P), hfilter, hfilterNot]
    exact Nat.add_le_add (G.sum_internal_arcs_le_choose P)
      (by simpa [Nat.mul_comm] using hexternal)
  apply capacity_arithmetic hp hpt htq
  simpa [Nat.mul_comm] using hlower.trans (hdouble.trans_le hupper)

theorem outNeighbors_subset_trap (x : V) : G.outNeighbors x ⊆ G.trap x := by
  intro y hy
  have hxy : G.Arc x y := G.mem_outNeighbors.mp hy
  exact G.mem_trap.mpr ⟨fun hyx => G.loopless x (hyx ▸ hxy), G.asymmetric hxy⟩

private theorem unreachable_eq_sdiff (v : V) :
    G.unreachable v = univ \ insert v (G.outNeighbors v ∪ G.secondNeighbors v) := by
  ext x
  simp only [G.mem_unreachable, mem_sdiff, mem_univ, true_and, mem_insert, mem_union,
    G.mem_outNeighbors, G.mem_secondNeighbors]
  constructor
  · rintro ⟨hxv, hvx, htwo⟩ (rfl | hout | hsecond)
    · exact hxv rfl
    · exact hvx hout
    · exact htwo hsecond.2
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact fun hxv => h (Or.inl hxv)
    · exact fun hvx => h (Or.inr (Or.inl hvx))
    · intro htwo
      have hvx : ¬G.Arc v x := fun harc => h (Or.inr (Or.inl harc))
      exact h (Or.inr (Or.inr ⟨hvx, htwo⟩))

/-- The vertex, first neighborhood, second neighborhood, and unreachable set partition `V`. -/
theorem neighborhood_card_identity (v : V) :
    (G.unreachable v).card + (1 + G.outDegree v + (G.secondNeighbors v).card) =
      Fintype.card V := by
  let R := insert v (G.outNeighbors v ∪ G.secondNeighbors v)
  have hvout : v ∉ G.outNeighbors v := by simp [G.loopless]
  have hvsecond : v ∉ G.secondNeighbors v := by
    simp only [G.mem_secondNeighbors, not_and_or]
    right
    push_neg
    intro y hvy hyv
    exact (G.asymmetric hvy) hyv
  have hdisj : Disjoint (G.outNeighbors v) (G.secondNeighbors v) := by
    rw [disjoint_left]
    intro x hxout hxsecond
    exact (G.mem_secondNeighbors.mp hxsecond).1 (G.mem_outNeighbors.mp hxout)
  have hRcard : R.card = 1 + G.outDegree v + (G.secondNeighbors v).card := by
    dsimp [R, outDegree]
    rw [card_insert_of_not_mem]
    · rw [card_union_of_disjoint hdisj]
      omega
    · exact Finset.not_mem_union.mpr ⟨hvout, hvsecond⟩
  rw [G.unreachable_eq_sdiff v]
  calc
    (univ \ R).card + (1 + G.outDegree v + (G.secondNeighbors v).card) =
        (univ \ R).card + R.card := congrArg ((univ \ R).card + ·) hRcard.symm
    _ = univ.card := card_sdiff_add_card_eq_card (subset_univ R)
    _ = Fintype.card V := rfl

private theorem trap_eq_sdiff (x : V) :
    G.trap x = univ \ insert x (G.inNeighbors x) := by
  ext y
  simp only [G.mem_trap, mem_sdiff, mem_univ, true_and, mem_insert, G.mem_inNeighbors]
  constructor
  · rintro ⟨hyx, harc⟩ (rfl | hy)
    · exact hyx rfl
    · exact harc hy
  · intro h
    push_neg at h
    exact h

/-- The trap consists of every vertex except the target and its inneighbors. -/
theorem trap_card_identity (x : V) :
    (G.trap x).card + (1 + G.inDegree x) = Fintype.card V := by
  let R := insert x (G.inNeighbors x)
  have hx : x ∉ G.inNeighbors x := by simp [G.loopless]
  have hRcard : R.card = 1 + G.inDegree x := by
    dsimp [R, inDegree]
    rw [card_insert_of_not_mem hx]
    omega
  rw [G.trap_eq_sdiff x]
  calc
    (univ \ R).card + (1 + G.inDegree x) = (univ \ R).card + R.card :=
      congrArg ((univ \ R).card + ·) hRcard.symm
    _ = univ.card := card_sdiff_add_card_eq_card (subset_univ R)
    _ = Fintype.card V := rfl

/-- Double-counting all arcs by source and by target. -/
theorem sum_outDegree_eq_sum_inDegree :
    (∑ v : V, G.outDegree v) = ∑ x : V, G.inDegree x := by
  simpa [outDegree, inDegree, outNeighbors, inNeighbors, bipartiteAbove, bipartiteBelow]
    using (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Arc
      (s := (univ : Finset V)) (t := (univ : Finset V)))

/-- Double-counting unreachable ordered pairs by source and target. -/
theorem sum_unreachable_eq_sum_predecessors :
    (∑ v : V, (G.unreachable v).card) = ∑ x : V, (G.predecessors x).card := by
  let r : V → V → Prop := fun v x => x ∈ G.unreachable v
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    (s := (univ : Finset V)) (t := (univ : Finset V))
  have habove : ∀ v, univ.bipartiteAbove r v = G.unreachable v := by
    intro v
    ext x
    simp [r]
  have hbelow : ∀ x, univ.bipartiteBelow r x = G.predecessors x := by
    intro x
    ext v
    simp [r]
  simpa only [habove, hbelow] using h

/-- At order `2δ+2`, total target slack is at most the number of
minimum-outdegree vertices.  This is equation (7) of the paper. -/
private theorem target_slack_ledger (δ : ℕ) (hmin : ∀ v, δ ≤ G.outDegree v)
    (hn : Fintype.card V = 2 * δ + 2) :
    (∑ x : V, ((G.trap x).card - δ)) ≤
      (univ.filter fun v => G.outDegree v = δ).card := by
  let L := univ.filter fun v => G.outDegree v = δ
  let ell := L.card
  let q : V → ℕ := fun x => (G.trap x).card - δ
  have hδtrap : ∀ x, δ ≤ (G.trap x).card := fun x =>
    (hmin x).trans (card_le_card (G.outNeighbors_subset_trap x))
  have hpoint : ∀ x, q x + G.inDegree x = δ + 1 := by
    intro x
    have htrap := G.trap_card_identity x
    have hxδ := hδtrap x
    have hsplit : (G.trap x).card = δ + q x := by
      dsimp [q]
      omega
    omega
  have hbalance : (∑ x : V, q x) + (∑ x : V, G.outDegree x) =
      Fintype.card V * (δ + 1) := by
    rw [G.sum_outDegree_eq_sum_inDegree]
    rw [← sum_add_distrib]
    calc
      (∑ x : V, (q x + G.inDegree x)) = ∑ _x : V, (δ + 1) := by
        apply sum_congr rfl
        intro x _
        exact hpoint x
      _ = Fintype.card V * (δ + 1) := by
        rw [sum_const_nat (fun _ _ => rfl)]
        rfl
  have hdegree : ∀ v, δ + 1 ≤ G.outDegree v + if v ∈ L then 1 else 0 := by
    intro v
    by_cases hv : v ∈ L
    · have : G.outDegree v = δ := by simpa [L] using hv
      simp [hv, this]
    · have hne : G.outDegree v ≠ δ := by
        intro heq
        exact hv (by simp [L, heq])
      have := hmin v
      simp only [hv, if_false, add_zero]
      omega
  have hindicator : (∑ v : V, if v ∈ L then 1 else 0) = ell := by
    have hfilter : (univ.filter fun v => v ∈ L) = L := by ext v; simp
    calc
      (∑ v : V, if v ∈ L then 1 else 0) = ∑ v ∈ univ.filter (fun v => v ∈ L), 1 :=
        (sum_filter (s := (univ : Finset V)) (fun v => v ∈ L) (fun _ => 1)).symm
      _ = ∑ _v ∈ L, 1 := by rw [hfilter]
      _ = L.card := (card_eq_sum_ones L).symm
      _ = ell := rfl
  have hlower : Fintype.card V * (δ + 1) ≤ (∑ v : V, G.outDegree v) + ell := by
    have hsum : (∑ _v : V, (δ + 1)) ≤
        ∑ v : V, (G.outDegree v + if v ∈ L then 1 else 0) := by
      apply sum_le_sum
      intro v _
      exact hdegree v
    calc
      Fintype.card V * (δ + 1) = ∑ _v : V, (δ + 1) := by
        rw [sum_const_nat (fun _ _ => rfl)]
        rfl
      _ ≤ ∑ v : V, (G.outDegree v + if v ∈ L then 1 else 0) := hsum
      _ = (∑ v : V, G.outDegree v) + (∑ v : V, if v ∈ L then 1 else 0) :=
        sum_add_distrib
      _ = (∑ v : V, G.outDegree v) + ell := congrArg ((∑ v : V, G.outDegree v) + ·) hindicator
  dsimp [q, ell, L] at hbalance hlower ⊢
  omega

/-- **Dense-case theorem for Seymour's second-neighborhood conjecture.**

If a finite oriented graph has minimum outdegree `δ` (expressed by a lower
bound attained at some vertex) and has exactly `2δ+2` vertices, then it has a
vertex whose exact second outneighborhood is at least as large as its
outneighborhood. -/
theorem dense_case_theorem (δ : ℕ) (hmin : ∀ v, δ ≤ G.outDegree v)
    (hattained : ∃ v, G.outDegree v = δ)
    (hn : Fintype.card V = 2 * δ + 2) :
    ∃ v, G.IsSeymour v := by
  by_contra hcounter
  push_neg at hcounter
  let L := univ.filter fun v => G.outDegree v = δ
  let ell := L.card
  let q : V → ℕ := fun x => (G.trap x).card - δ
  let I := ∑ v : V, (G.unreachable v).card
  have hL : L.Nonempty := by
    obtain ⟨v, hv⟩ := hattained
    exact ⟨v, by simp [L, hv]⟩
  have hell : 0 < ell := by simpa [ell, card_pos] using hL
  have hdemand : ∀ v ∈ L, 2 ≤ (G.unreachable v).card := by
    intro v hv
    have hvdeg : G.outDegree v = δ := by simpa [L] using hv
    have hnoseymour := hcounter v
    have hsecond : (G.secondNeighbors v).card < G.outDegree v :=
      Nat.lt_of_not_ge hnoseymour
    have hpartition := G.neighborhood_card_identity v
    omega
  have hIlower : 2 * ell ≤ I := by
    have hrestricted : ell * 2 ≤ ∑ v ∈ L, (G.unreachable v).card := by
      simpa [ell, nsmul_eq_mul] using
        L.card_nsmul_le_sum (fun v => (G.unreachable v).card) 2 hdemand
    have hsubset : (∑ v ∈ L, (G.unreachable v).card) ≤ I := by
      dsimp [I]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ L) (fun _ _ _ => Nat.zero_le _)
    simpa [Nat.mul_comm] using hrestricted.trans hsubset
  let S := univ.filter fun x => (G.predecessors x).Nonempty
  have hS : S.Nonempty := by
    obtain ⟨v, hvL⟩ := hL
    have hvU : (G.unreachable v).Nonempty := card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two (hdemand v hvL))
    obtain ⟨x, hxU⟩ := hvU
    refine ⟨x, ?_⟩
    simp only [S, mem_filter, mem_univ, true_and]
    exact ⟨v, G.mem_predecessors.mpr hxU⟩
  have hIrepr : I = ∑ x ∈ S, (G.predecessors x).card := by
    dsimp [I]
    rw [G.sum_unreachable_eq_sum_predecessors]
    have hfilter := sum_filter (s := (univ : Finset V))
      (fun x => (G.predecessors x).Nonempty) (fun x => (G.predecessors x).card)
    rw [show S = univ.filter (fun x => (G.predecessors x).Nonempty) by rfl]
    rw [hfilter]
    apply sum_congr rfl
    intro x _
    by_cases hx : (G.predecessors x).Nonempty
    · simp [hx]
    · have hz : (G.predecessors x).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hx)
      simp [hx, hz]
  have hcapacity : ∀ x ∈ S,
      (G.predecessors x).card < 2 * q x := by
    intro x hx
    have hxP : (G.predecessors x).Nonempty := by simpa [S] using hx
    have hcap := G.fixed_target_capacity δ hmin x hxP
    dsimp [q]
    omega
  have hIcapacity : I < 2 * (∑ x : V, q x) := by
    have hstrict : (∑ x ∈ S, (G.predecessors x).card) < ∑ x ∈ S, 2 * q x :=
      sum_lt_sum_of_nonempty hS hcapacity
    have hsubset : (∑ x ∈ S, 2 * q x) ≤ ∑ x : V, 2 * q x :=
      sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => Nat.zero_le _)
    calc
      I = ∑ x ∈ S, (G.predecessors x).card := hIrepr
      _ < ∑ x ∈ S, 2 * q x := hstrict
      _ ≤ ∑ x : V, 2 * q x := hsubset
      _ = 2 * (∑ x : V, q x) := by rw [mul_sum]
  have hQledger : (∑ x : V, q x) ≤ ell := by
    simpa [q, ell, L] using G.target_slack_ledger δ hmin hn
  omega

end OrientedGraph

end DenseCaseSNC
