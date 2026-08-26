import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ConcreteRadialHandle

/-! # Concrete least-favorable handle certificates

This module packages ambient membership and coupling certificates for handles
whose fields are the canonical padded binary constructions.
-/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Set

-- @node: exactEmbeddingMembership_of_affinePadded
/-- If [the cap satisfies the exact-embedding bound](hyp:hcap) and [the padded dimension satisfies
  the cap bound](hyp:hcapd) and [the overlap constant is positive](hyp:he0) and [the overlap
  constant is below one half](hyp:he1) and [the outcome scale satisfies its stated bound](hyp:hM)
  and [the specified embedding certificate holds](hyp:hembedding), [a handle using the canonical
  padded affine exact embedding has the required radius-zero ambient membership
  certificate](goal). -/
lemma exactEmbeddingMembership_of_affinePadded {n d : ℕ}
    {epsilon M sigma : ℝ} (H : LeastFavorableHandle n d epsilon M sigma)
    (hcap : 0 < H.exactCap) (hcapd : H.exactCap ≤ d)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) (hM : 1 ≤ M)
    (hembedding : ∀ P, H.exactEmbedding P =
      affineBinaryRealLaw M (binaryPadLaw hcapd P.1)) :
    ExactEmbeddingMembership H := by
  intro P _hP
  refine ⟨affineBinaryPaddedLaw_model hcapd hcap P.1 he0 he1 hM
    (by norm_num) (by norm_num) P.2, ?_⟩
  exact (hembedding P).symm

-- @node: radialEmbeddingMembership_of_contractedPadded
/-- If [the padded dimension satisfies the cap bound](hyp:hcapd) and [the overlap constant is
  positive](hyp:he0) and [the overlap constant is below one half](hyp:he1) and [the outcome scale
  satisfies its stated bound](hyp:hM) and [the heterogeneity radius is nonnegative](hyp:hs0) and
  [the heterogeneity radius is at most two](hyp:hs2) and [the specified embedding certificate
  holds](hyp:hembedding), [a handle using the padded Bernoulli-contracted affine embedding has the
  required radius-indexed ambient membership certificate](goal). -/
lemma radialEmbeddingMembership_of_contractedPadded {n d : ℕ}
    {epsilon M sigma : ℝ} (H : LeastFavorableHandle n d epsilon M sigma)
    (hcapd : H.radialCap ≤ d)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) (hM : 1 ≤ M)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2)
    (hembedding : ∀ P, H.radialEmbedding P =
      affineBinaryRealLaw M
        (binaryPadLaw hcapd (radialContractedBinaryLaw P.1 sigma hs0 hs2))) :
    RadialEmbeddingMembership H := by
  intro P _hP
  refine ⟨radialPaddedAffineLaw_model hcapd P he0 he1 hM hs0 hs2, ?_⟩
  exact (hembedding P).symm

-- @node: exactCouplingCertificate_of_independentFullPMF
/-- If [the specified full-data coupling is available](hyp:hcoupling), [the canonical independent
  full-data lift packages the exact coupling certificate of a concrete handle](goal). -/
lemma exactCouplingCertificate_of_independentFullPMF {n d : ℕ}
    {epsilon M sigma : ℝ} (H : LeastFavorableHandle n d epsilon M sigma)
    (hcoupling : ∀ P, H.exactCoupling P =
      (binaryIndependentFullPMF P.1).toMeasure) :
    ExactCouplingCertificate H := by
  intro P _hP
  rw [hcoupling P]
  exact binaryIndependentFullCoupling_spec P.1

-- @node: radialCouplingCertificate_of_independentFullPMF
/-- If [the specified full-data coupling is available](hyp:hcoupling), [the same canonical
  independent full-data lift packages the radial source coupling certificate of a concrete
  handle](goal). -/
lemma radialCouplingCertificate_of_independentFullPMF {n d : ℕ}
    {epsilon M sigma : ℝ} (H : LeastFavorableHandle n d epsilon M sigma)
    (hcoupling : ∀ P, H.radialCoupling P =
      (binaryIndependentFullPMF P.1).toMeasure) :
    RadialCouplingCertificate H := by
  intro P _hP
  rw [hcoupling P]
  exact binaryIndependentFullCoupling_spec P.1

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
