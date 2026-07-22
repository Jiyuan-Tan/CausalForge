/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.MarkovEquiv.CoveredReversal

/-! # Covered-edge decomposition (AMP Lemma 3.2) + Verma–Pearl hard direction

This file assembles the covered-edge route to the hard direction of Verma–Pearl:
DAGs with the same skeleton and the same immoralities are Markov equivalent. Following
Andersson–Madigan–Perlman (1997) Lemma 3.2, two such DAGs are connected by a finite chain of
single covered-edge reversals; `markovEquiv_flipEdge` (`CoveredReversal.lean`) handles each
step, and `MarkovEquiv.trans` chains them. The induction is on the number of oppositely
oriented edges (`edgeDiffCount`).
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `SameSkeleton` is symmetric. -/
theorem SameSkeleton.symm {G₁ G₂ : DAG V} (h : SameSkeleton G₁ G₂) : SameSkeleton G₂ G₁ :=
  fun a b => (h a b).symm

/-- `SameSkeleton` is transitive. -/
theorem SameSkeleton.trans {G₁ G₂ G₃ : DAG V} (h₁ : SameSkeleton G₁ G₂)
    (h₂ : SameSkeleton G₂ G₃) : SameSkeleton G₁ G₃ := fun a b => (h₁ a b).trans (h₂ a b)

/-- `SameImmoralities` is symmetric. -/
theorem SameImmoralities.symm {G₁ G₂ : DAG V} (h : SameImmoralities G₁ G₂) :
    SameImmoralities G₂ G₁ := fun a b c => (h a b c).symm

/-- `SameImmoralities` is transitive. -/
theorem SameImmoralities.trans {G₁ G₂ G₃ : DAG V} (h₁ : SameImmoralities G₁ G₂)
    (h₂ : SameImmoralities G₂ G₃) : SameImmoralities G₁ G₃ :=
  fun a b c => (h₁ a b c).trans (h₂ a b c)

/-- **Edge-congruence for Markov equivalence.** DAGs with the same directed-edge relation are
Markov equivalent (d-separation depends only on the edge relation). -/
theorem markovEquiv_of_same_edge {G₁ G₂ : DAG V}
    (he : ∀ u w, G₁.edge u w ↔ G₂.edge u w) : MarkovEquiv G₁ G₂ := by
  intro X Y Z hXY hXZ hYZ
  have h := DAG.hasActivePath_edge_congr he X Y Z
  rw [← DAG.not_dSep_iff_hasActivePath G₁ X Y Z hXY hXZ hYZ,
    ← DAG.not_dSep_iff_hasActivePath G₂ X Y Z hXY hXZ hYZ] at h
  exact not_iff_not.mp h

/-- The directed edges of `G₁` that are absent from `G₂`. -/
def edgeDiff (G₁ G₂ : DAG V) : Finset (V × V) :=
  Finset.univ.filter (fun p => G₁.edge p.1 p.2 ∧ ¬ G₂.edge p.1 p.2)

/-- Number of directed edges of `G₁` absent from `G₂`. -/
def edgeDiffCount (G₁ G₂ : DAG V) : ℕ := (edgeDiff G₁ G₂).card

/-- With a shared skeleton, an empty edge-difference forces equal edge relations. -/
theorem same_edge_of_edgeDiff_empty {G₁ G₂ : DAG V} (hskel : SameSkeleton G₁ G₂)
    (h : edgeDiff G₁ G₂ = ∅) : ∀ u w, G₁.edge u w ↔ G₂.edge u w := by
  have hsub : ∀ u w, G₁.edge u w → G₂.edge u w := by
    intro u w he
    by_contra hne
    have hmem : (u, w) ∈ edgeDiff G₁ G₂ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hne⟩
    rw [h] at hmem; simp at hmem
  intro u w
  refine ⟨hsub u w, fun he2 => ?_⟩
  rcases (hskel u w).mpr (Or.inl he2) with h1 | h1
  · exact h1
  · exact absurd (hsub w u h1) (G₂.asymm he2)

/-- **AMP Lemma 3.2 (existence).** Same skeleton + same immoralities, with at least one
oppositely oriented edge, yields a *covered* such edge. The proof chooses a head of a
reversed edge that is minimal in the first graph's topological order, then a tail into that
head that is maximal among reversed tails; the skeleton and immorality hypotheses force this
edge to have the same non-tail parents at both endpoints. -/
theorem exists_covered_reversed_edge {G₁ G₂ : DAG V} (hskel : SameSkeleton G₁ G₂)
    (himm : SameImmoralities G₁ G₂) {a₀ b₀ : V} (h₀ : G₁.edge a₀ b₀) (h₀' : G₂.edge b₀ a₀) :
    ∃ a b, G₁.edge a b ∧ G₂.edge b a ∧ G₁.IsCoveredEdge a b := by
  let Heads : Finset V :=
    Finset.univ.filter (fun y => ∃ x, G₁.edge x y ∧ G₂.edge y x)
  have hHead0 : b₀ ∈ Heads := by
    change b₀ ∈ Finset.univ.filter (fun y => ∃ x, G₁.edge x y ∧ G₂.edge y x)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a₀, h₀, h₀'⟩⟩
  have hHeads_ne : Heads.Nonempty := ⟨b₀, hHead0⟩
  obtain ⟨b, hbHead, hbmin⟩ := Finset.exists_min_image Heads G₁.topoOrder hHeads_ne
  have hbWitness : ∃ x, G₁.edge x b ∧ G₂.edge b x := by
    have hbHead' : b ∈ Finset.univ.filter (fun y => ∃ x, G₁.edge x y ∧ G₂.edge y x) := by
      simpa [Heads] using hbHead
    exact (Finset.mem_filter.mp hbHead').2
  obtain ⟨x, hxb₁, hbx₂⟩ := hbWitness
  let Tails : Finset V := Finset.univ.filter (fun x => G₁.edge x b ∧ G₂.edge b x)
  have hxTail : x ∈ Tails := by
    change x ∈ Finset.univ.filter (fun x => G₁.edge x b ∧ G₂.edge b x)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxb₁, hbx₂⟩
  have hTails_ne : Tails.Nonempty := ⟨x, hxTail⟩
  obtain ⟨a, haTail, hamax⟩ := Finset.exists_max_image Tails G₁.topoOrder hTails_ne
  have haRev : G₁.edge a b ∧ G₂.edge b a := by
    have haTail' : a ∈ Finset.univ.filter (fun x => G₁.edge x b ∧ G₂.edge b x) := by
      simpa [Tails] using haTail
    exact (Finset.mem_filter.mp haTail').2
  refine ⟨a, b, haRev.1, haRev.2, haRev.1, ?_⟩
  intro c hca_ne
  by_contra hiff
  by_cases hca : G₁.edge c a
  · by_cases hcb : G₁.edge c b
    · exact hiff ⟨fun _ => hcb, fun _ => hca⟩
    · have hnotG1Ucb : ¬ G₁.UAdj c b := by
        intro hU
        rcases hU with hcb' | hbc
        · exact hcb hcb'
        · have hcbTop : G₁.topoOrder c < G₁.topoOrder b :=
            lt_trans (G₁.topoOrder_lt c a hca) (G₁.topoOrder_lt a b haRev.1)
          exact (Nat.lt_irrefl _) (lt_trans hcbTop (G₁.topoOrder_lt b c hbc))
      have hnotG2Ucb : ¬ G₂.UAdj c b := by
        intro hU
        exact hnotG1Ucb ((hskel c b).mpr hU)
      have hcb_ne : c ≠ b := by
        intro heq
        subst c
        exact (G₁.asymm haRev.1) hca
      have hnotG2ca : ¬ G₂.edge c a := by
        intro hca₂
        have him₂ : G₂.IsImmorality c a b := ⟨hca₂, haRev.2, hnotG2Ucb, hcb_ne⟩
        have him₁ : G₁.IsImmorality c a b := (himm c a b).mpr him₂
        exact (G₁.asymm haRev.1) him₁.2.1
      have hU2ca : G₂.UAdj c a := (hskel c a).mp (Or.inl hca)
      have hac₂ : G₂.edge a c := hU2ca.resolve_left hnotG2ca
      have haHead : a ∈ Heads := by
        change a ∈ Finset.univ.filter (fun y => ∃ x, G₁.edge x y ∧ G₂.edge y x)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨c, hca, hac₂⟩⟩
      have hle : G₁.topoOrder b ≤ G₁.topoOrder a := hbmin a haHead
      exact (not_lt_of_ge hle) (G₁.topoOrder_lt a b haRev.1)
  · by_cases hcb : G₁.edge c b
    · have hac_ne : a ≠ c := fun heq => hca_ne heq.symm
      have hUac : G₁.UAdj a c := by
        by_contra hnotU
        have him₁ : G₁.IsImmorality a b c := ⟨haRev.1, hcb, hnotU, hac_ne⟩
        have him₂ : G₂.IsImmorality a b c := (himm a b c).mp him₁
        exact (G₂.asymm haRev.2) him₂.1
      have hac : G₁.edge a c := hUac.resolve_right hca
      have hrevNext : G₂.edge b c ∨ G₂.edge c a := by
        by_cases hbc₂ : G₂.edge b c
        · exact Or.inl hbc₂
        · by_cases hca₂ : G₂.edge c a
          · exact Or.inr hca₂
          · have hU2cb : G₂.UAdj c b := (hskel c b).mp (Or.inl hcb)
            have hcb₂ : G₂.edge c b := hU2cb.resolve_right hbc₂
            have hU2ac : G₂.UAdj a c := (hskel a c).mp (Or.inl hac)
            have hac₂ : G₂.edge a c := hU2ac.resolve_right hca₂
            have hcycle : G₂.topoOrder b < G₂.topoOrder b :=
              lt_trans (G₂.topoOrder_lt b a haRev.2)
                (lt_trans (G₂.topoOrder_lt a c hac₂) (G₂.topoOrder_lt c b hcb₂))
            exact False.elim ((Nat.lt_irrefl _) hcycle)
      rcases hrevNext with hbc₂ | hca₂
      · have hcTail : c ∈ Tails := by
          change c ∈ Finset.univ.filter (fun x => G₁.edge x b ∧ G₂.edge b x)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcb, hbc₂⟩
        have hle : G₁.topoOrder c ≤ G₁.topoOrder a := hamax c hcTail
        exact (not_lt_of_ge hle) (G₁.topoOrder_lt a c hac)
      · have hcHead : c ∈ Heads := by
          change c ∈ Finset.univ.filter (fun y => ∃ x, G₁.edge x y ∧ G₂.edge y x)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, hac, hca₂⟩⟩
        have hle : G₁.topoOrder b ≤ G₁.topoOrder c := hbmin c hcHead
        exact (not_lt_of_ge hle) (G₁.topoOrder_lt c b hcb)
    · exact hiff ⟨fun h => False.elim (hca h), fun h => False.elim (hcb h)⟩

/-- Flipping a covered, oppositely oriented edge strictly decreases the edge-difference count
(it fixes exactly the pair `(a,b)` and changes nothing else). -/
theorem edgeDiffCount_flipEdge_lt {G₁ G₂ : DAG V} {a b : V}
    (hcov : G₁.IsCoveredEdge a b) (hba : G₂.edge b a) :
    edgeDiffCount (DAG.flipEdge hcov) G₂ < edgeDiffCount G₁ G₂ := by
  have hsub : edgeDiff (DAG.flipEdge hcov) G₂ ⊆ edgeDiff G₁ G₂ := by
    intro p hp
    rw [edgeDiff, Finset.mem_filter] at hp ⊢
    obtain ⟨_, hedge, hnot⟩ := hp
    rw [DAG.flipEdge_edge] at hedge
    rcases hedge with ⟨h1, _⟩ | ⟨hb, ha⟩
    · exact ⟨Finset.mem_univ _, h1, hnot⟩
    · exact absurd (by rw [hb, ha]; exact hba) hnot
  unfold edgeDiffCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsub]
  refine ⟨(a, b), ?_, ?_⟩
  · rw [edgeDiff, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcov.1, G₂.asymm hba⟩
  · rw [edgeDiff, Finset.mem_filter]
    rintro ⟨_, hedge, _⟩
    rw [DAG.flipEdge_edge] at hedge
    rcases hedge with ⟨_, hnotab⟩ | ⟨hb, _⟩
    · exact hnotab ⟨rfl, rfl⟩
    · exact hcov.ne hb

private theorem markovEquiv_covered_aux (G₂ : DAG V) :
    ∀ (n : ℕ) (G₁ : DAG V), SameSkeleton G₁ G₂ → SameImmoralities G₁ G₂ →
      edgeDiffCount G₁ G₂ = n → MarkovEquiv G₁ G₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G₁ hskel himm hn
    rcases Finset.eq_empty_or_nonempty (edgeDiff G₁ G₂) with hempty | ⟨p, hp⟩
    · exact markovEquiv_of_same_edge (same_edge_of_edgeDiff_empty hskel hempty)
    · obtain ⟨ha0b0, hnotG2⟩ := (Finset.mem_filter.mp hp).2
      have hUadj2 : G₂.UAdj p.1 p.2 := (hskel p.1 p.2).mp (Or.inl ha0b0)
      have hb0a0 : G₂.edge p.2 p.1 := hUadj2.resolve_left hnotG2
      obtain ⟨a, b, hab1, hba2, hcov⟩ := exists_covered_reversed_edge hskel himm ha0b0 hb0a0
      have hflip : MarkovEquiv G₁ (DAG.flipEdge hcov) := DAG.markovEquiv_flipEdge hcov
      have hskel' : SameSkeleton (DAG.flipEdge hcov) G₂ :=
        (DAG.flipEdge_sameSkeleton hcov).symm.trans hskel
      have himm' : SameImmoralities (DAG.flipEdge hcov) G₂ :=
        (DAG.flipEdge_sameImmoralities hcov).symm.trans himm
      have hlt : edgeDiffCount (DAG.flipEdge hcov) G₂ < edgeDiffCount G₁ G₂ :=
        edgeDiffCount_flipEdge_lt hcov hba2
      exact hflip.trans
        (ih (edgeDiffCount (DAG.flipEdge hcov) G₂) (hn ▸ hlt) (DAG.flipEdge hcov) hskel' himm' rfl)

/-- **Verma–Pearl hard direction (covered-edge route).** DAGs with the same skeleton and the
same immoralities are Markov equivalent — proven via AMP Lemma 3.2 (covered-edge reversals),
independent of the moralization/ancestral kernel. -/
theorem markovEquiv_of_sameSkeleton_sameImmoralities_covered {G₁ G₂ : DAG V}
    (hskel : SameSkeleton G₁ G₂) (himm : SameImmoralities G₁ G₂) : MarkovEquiv G₁ G₂ :=
  markovEquiv_covered_aux G₂ (edgeDiffCount G₁ G₂) G₁ hskel himm rfl

end Causalean
