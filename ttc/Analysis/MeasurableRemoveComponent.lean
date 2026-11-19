import ttc.Analysis.ReferenceProgram

/-!
# Measurability of component removal

Removing copies lying in a fixed polytope is a measurable deterministic state
transition.
-/

namespace ttc

/--
Filtering an incoming TTC state against a fixed component is measurable.

INTERNAL: deterministic state-transition measurability for `processComponent`.
-/
lemma measurable_removeComponent {n : Nat} (P : PolytopeData n) :
    Measurable (fun s : TTCState n => s.removeComponent P) := by
  classical
  have hcoords : Measurable
      (fun s : TTCState n => (s.p, s.X, s.nextLabel)) :=
    comap_measurable _
  have hrate : Measurable (fun s : TTCState n => s.p) :=
    measurable_fst.comp hcoords
  have hsamples : Measurable (fun s : TTCState n => s.X) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hnext : Measurable (fun s : TTCState n => s.nextLabel) :=
    (measurable_snd.comp measurable_snd).comp hcoords
  have hfilter : Measurable (fun s : TTCState n =>
      s.X.filter (fun copy => copy.2.toPoint ∉ P.carrier)) := by
    rw [measurable_finset_iff]
    intro copy
    have hm := (measurable_finset_mem copy).comp hsamples
    change Measurable (fun s : TTCState n => copy ∈ s.X) at hm
    simpa only [Finset.mem_filter] using
      hm.and (measurable_const :
        Measurable (fun _ : TTCState n => copy.2.toPoint ∉ P.carrier))
  rw [measurable_comap_iff]
  change Measurable (fun s : TTCState n =>
    (s.p, s.X.filter (fun copy => copy.2.toPoint ∉ P.carrier), s.nextLabel))
  exact hrate.prodMk (hfilter.prodMk hnext)

end ttc

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · reduced finite-set measurability to membership in each fixed copy
-/
