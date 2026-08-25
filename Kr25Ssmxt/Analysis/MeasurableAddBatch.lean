import Kr25Ssmxt.Model.Pseudocode

/-!
# Joint measurability of batch insertion

For a fixed batch size, inserting generated points is jointly measurable in the
incoming state and batch coordinates.
-/

namespace Kr25Ssmxt

/--
Adding a fixed-size batch is jointly measurable in the state and point family.

INTERNAL: deterministic state-transition measurability after sampling.
-/
lemma measurable_addBatch {n count : Nat} :
    Measurable (fun z : TTCState n × (Fin count → LatticePoint n) =>
      z.1.addBatch z.2) := by
  classical
  have hstateCoords : Measurable (fun z : TTCState n × (Fin count → LatticePoint n) =>
      (z.1.rate, z.1.samples, z.1.nextLabel)) :=
    (comap_measurable _).comp measurable_fst
  have hrate : Measurable (fun z : TTCState n × (Fin count → LatticePoint n) =>
      z.1.rate) :=
    measurable_fst.comp hstateCoords
  have hsamples : Measurable (fun z : TTCState n × (Fin count → LatticePoint n) =>
      z.1.samples) :=
    (measurable_fst.comp measurable_snd).comp hstateCoords
  have hnext : Measurable (fun z : TTCState n × (Fin count → LatticePoint n) =>
      z.1.nextLabel) :=
    (measurable_snd.comp measurable_snd).comp hstateCoords
  have hadded : Measurable (fun z : TTCState n × (Fin count → LatticePoint n) =>
      z.1.samples ∪ Finset.univ.image
        (fun i : Fin count => (z.1.nextLabel + i.val, z.2 i))) := by
    rw [measurable_finset_iff]
    intro copy
    have hold : Measurable (fun z : TTCState n × (Fin count → LatticePoint n) =>
        copy ∈ z.1.samples) :=
      (measurable_finset_mem copy).comp hsamples
    have hfresh : ∀ i : Fin count,
        Measurable (fun z : TTCState n × (Fin count → LatticePoint n) =>
          (z.1.nextLabel + i.val, z.2 i)) := by
      intro i
      exact ((measurable_of_countable (fun label : Nat => label + i.val)).comp hnext).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
    simpa only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] using
      hold.or (Measurable.exists fun i => (hfresh i).eq_const copy)
  unfold TTCState.addBatch
  rw [measurable_comap_iff]
  change Measurable (fun z : TTCState n × (Fin count → LatticePoint n) =>
    (z.1.rate,
      z.1.samples ∪ Finset.univ.image
        (fun i : Fin count => (z.1.nextLabel + i.val, z.2 i)),
      z.1.nextLabel + count))
  exact hrate.prodMk (hadded.prodMk
    ((measurable_of_countable (fun label : Nat => label + count)).comp hnext))

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · reduced finite-set measurability to old-or-fresh membership
-/
