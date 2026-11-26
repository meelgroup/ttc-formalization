/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.FuelFold

/-!
# More fuel changes nothing that finished

`FuelLE p q` says that wherever `p` gives a result, `q` runs exactly as `p` does.  The
program with more fuel is above the program with less (`fuelLE_estimatorT`): a run that
finishes keeps its output and operation count when given more fuel.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {d : ℕ} {α β : Type}

/-- **Wherever `p` finishes, `q` runs exactly as `p`.** -/
def FuelLE (p q : Tree d α) : Prop :=
  ∀ b t, (exec p b t).1.isSome → exec q b t = exec p b t

theorem FuelLE.refl (p : Tree d α) : FuelLE p p := fun _ _ _ => rfl

theorem fuelLE_fail (q : Tree d α) : FuelLE .fail q := fun _ _ h => by simp [exec] at h

theorem FuelLE.bind {p q : Tree d α} {f g : α → Tree d β} (hpq : FuelLE p q)
    (hfg : ∀ a, FuelLE (f a) (g a)) : FuelLE (p.bind f) (q.bind g) := by
  intro b t h
  rw [exec_bind] at h ⊢
  rw [exec_bind]
  rcases hp : exec p b t with ⟨_ | a, m, b', t'⟩
  · rw [hp] at h; simp at h
  · have hq := hpq b t (by rw [hp]; rfl)
    rw [hp] at hq h
    rw [hq]
    simp only at h ⊢
    rw [hfg a b' t' h]

theorem fuelLE_ite (c : Bool) {p p' q q' : Tree d α} (hp : FuelLE p p') (hq : FuelLE q q') :
    FuelLE (if c then p else q) (if c then p' else q') := by cases c <;> assumption

theorem fuelLE_step {δ : Type} (c : Prog δ) {k k' : δ → Tree d α} (h : ∀ x, FuelLE (k x) (k' x)) :
    FuelLE (Tree.step c k) (Tree.step c k') := by
  intro b t hs
  have := h c.val b t hs
  simp only [exec] at hs ⊢
  rw [this]

theorem fuelLE_foldlM {ι : Type} {g g' : β → ι → Tree d β} (h : ∀ b x, FuelLE (g b x) (g' b x)) :
    ∀ (l : List ι) (b : β), FuelLE (l.foldlM g b) (l.foldlM g' b)
  | [], b => FuelLE.refl _
  | x :: l, b => by
      simp only [List.foldlM_cons]
      exact FuelLE.bind (h b x) fun b' => fuelLE_foldlM h l b'

theorem fuelLE_loopRounds {γ : Type} {body body' : β → Tree d (β ⊕ γ)}
    (h : ∀ y, FuelLE (body y) (body' y)) :
    ∀ (k : ℕ) (y : β), FuelLE (loopRounds body k y) (loopRounds body' k y)
  | 0, y => FuelLE.refl _
  | k + 1, y => FuelLE.bind (h y) fun r => by
      rcases r with y' | c
      · exact fuelLE_loopRounds h k y'
      · exact FuelLE.refl _

theorem fuelLE_loopTree {γ : Type} (count : Num ℕ) {body body' : β → Tree d (β ⊕ γ)}
    (h : ∀ y, FuelLE (body y) (body' y)) (init : β) :
    FuelLE (loopTree count body init) (loopTree count body' init) :=
  fuelLE_step _ fun _ => fuelLE_loopRounds h _ init

/-! ## The fuel-dependent pieces -/

theorem fuelLE_halveT (K : Params) :
    ∀ (f f' : ℕ), f ≤ f' → ∀ (p : Num ℝ) (X : List (Fin d → Num ℤ)) (size N : Num ℕ),
      FuelLE (halveT K f p X size N) (halveT K f' p X size N)
  | 0, _, _, _, _, _, _ => fuelLE_fail _
  | f + 1, 0, h, _, _, _, _ => absurd h (by omega)
  | f + 1, f' + 1, h, p, X, size, N => by
      unfold halveT
      refine FuelLE.bind (FuelLE.refl _) fun stop => fuelLE_ite _ (FuelLE.refl _) ?_
      refine FuelLE.bind (FuelLE.refl _) fun r => FuelLE.bind (FuelLE.refl _) fun N' => ?_
      exact FuelLE.bind (FuelLE.refl _) fun p' =>
        fuelLE_halveT K f f' (by omega) _ _ _ _

theorem fuelLE_sampleUntilAccepted (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) :
    ∀ (f f' : ℕ), f ≤ f' →
      FuelLE (sampleUntilAcceptedT L W scaled dimN f) (sampleUntilAcceptedT L W scaled dimN f')
  | 0, _, _ => fuelLE_fail _
  | f + 1, 0, h => absurd h (by omega)
  | f + 1, f' + 1, h => FuelLE.bind (FuelLE.refl _) fun r => by
      rcases r with _ | z
      · exact fuelLE_sampleUntilAccepted L W scaled dimN f f' (by omega)
      · exact FuelLE.refl _

theorem fuelLE_stepT (K : Params) (L : Loaded d) {f f' : ℕ} (h : f ≤ f') (s : State d) :
    FuelLE (stepT (cv18T d) f K L s) (stepT (cv18T d) f' K L s) := by
  rw [stepT_eq, stepT_eq]
  refine FuelLE.bind (FuelLE.refl _) fun _ => FuelLE.bind (FuelLE.refl _) fun _ =>
    FuelLE.bind (FuelLE.refl _) fun _ => FuelLE.bind (FuelLE.refl _) fun t =>
      FuelLE.bind (FuelLE.refl _) fun scaled => FuelLE.bind (FuelLE.refl _) fun q => ?_
  rw [tailT_eq, tailT_eq]
  refine FuelLE.bind (FuelLE.refl _) fun _ => FuelLE.bind (FuelLE.refl _) fun N =>
    FuelLE.bind (fuelLE_halveT K f f' h _ _ _ _) fun hh => ?_
  unfold sampleT
  refine FuelLE.bind (FuelLE.refl _) fun W => FuelLE.bind ?_ fun _ => FuelLE.refl _
  refine fuelLE_loopTree _ (fun acc => ?_) _
  unfold sampleBody
  exact FuelLE.bind (fuelLE_sampleUntilAccepted _ _ _ _ f f' h) fun _ => FuelLE.refl _

/-- **The program with more fuel runs as the program with less, wherever that finishes.** -/
theorem fuelLE_estimatorT {f f' : ℕ} (h : f ≤ f') (cs : List (ttc.ComponentInput d))
    (eps delta : ℝ) :
    FuelLE (estimatorT (cv18T d) f cs eps delta) (estimatorT (cv18T d) f' cs eps delta) := by
  cases cs with
  | nil => exact FuelLE.refl _
  | cons c cs =>
      rw [estimatorT_cons f _ (List.cons_ne_nil _ _), estimatorT_cons f' _ (List.cons_ne_nil _ _)]
      refine FuelLE.bind (FuelLE.refl _) fun Ls => FuelLE.bind (FuelLE.refl _) fun K =>
        FuelLE.bind (FuelLE.refl _) fun zero => FuelLE.bind ?_ fun _ => FuelLE.refl _
      exact fuelLE_foldlM (fun s L => fuelLE_stepT K L h s) Ls _

end ttc.Tape
