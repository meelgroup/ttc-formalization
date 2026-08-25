import Kr25Ssmxt.Analysis.MeasurableSampleAddFixed

/-!
# Count-indexed sampling and insertion tail

The fixed-count sampling kernels are glued across the discrete pending-count
coordinate without forming an ill-typed dependent function space.
-/

namespace Kr25Ssmxt

/--
The final sampling, insertion, and thinning tail is measurable jointly in the
incoming state and the (discrete) generated batch size.

INTERNAL: countable gluing of the fixed-count `processComponent` tails.
-/
lemma measurable_sample_add_by_count {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (hadd : ∀ count, Measurable
      (fun z : TTCState n × (Fin count → LatticePoint n) => z.1.addBatch z.2))
    (hthin : Measurable
      (fun z : TTCState n × Nat => thinUntil z.1 z.2 threshold)) :
    Measurable (fun z : TTCState n × Nat =>
      (O.generateSamples P z.2 b epsilonPrime deltaPrime).bind fun batch =>
        (thinUntil (z.1.addBatch batch.2) 0 threshold).map Prod.fst) := by
  apply measurable_from_prod_countable_left
  intro count
  exact measurable_sample_add_fixed O b count epsilonPrime deltaPrime threshold P
    (hadd count) hthin

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · glued the fixed-count sections across measurable singleton counts
-/
