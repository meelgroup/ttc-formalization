/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.Operations

/-! # Specification lemmas for TTC's local real-RAM operations -/

set_option autoImplicit false

namespace Arlib.Computation.Num

universe u

/-- A held number is determined by its mathematical value. -/
theorem get_injective {α : Type u} : Function.Injective (get : Num α → α) := by
  rintro ⟨a⟩ ⟨b⟩ h
  cases h
  rfl

@[ext] theorem ext {α : Type u} {x y : Num α} (h : x.get = y.get) : x = y :=
  get_injective h

@[simp] theorem cost_min {κ κₛ α : Type} [DecidableEq κ] [NumOps κ] [Min α]
    (x y : Num α) :
    (min x y : Charged κ κₛ (Num α)).cost = CostVec.one (numOpcode κ .min) := rfl

variable {κ κₛ : Type} [DecidableEq κ] [RealOps κ]

@[simp] theorem get_cast (k : Num ℕ) :
    (cast k : Charged κ κₛ (Num ℝ)).val.get = (k.get : ℝ) := rfl

@[simp] theorem cost_cast (k : Num ℕ) :
    (cast k : Charged κ κₛ (Num ℝ)).cost = CostVec.one (realOpcode κ .cast) := rfl

@[simp] theorem get_sqrt (x : Num ℝ) :
    (sqrt x : Charged κ κₛ (Num ℝ)).val.get = Real.sqrt x.get := rfl

@[simp] theorem cost_sqrt (x : Num ℝ) :
    (sqrt x : Charged κ κₛ (Num ℝ)).cost = CostVec.one (realOpcode κ .sqrt) := rfl

@[simp] theorem get_exp (x : Num ℝ) :
    (exp x : Charged κ κₛ (Num ℝ)).val.get = Real.exp x.get := rfl

@[simp] theorem cost_exp (x : Num ℝ) :
    (exp x : Charged κ κₛ (Num ℝ)).cost = CostVec.one (realOpcode κ .exp) := rfl

@[simp] theorem get_log (x : Num ℝ) :
    (log x : Charged κ κₛ (Num ℝ)).val.get = Real.log x.get := rfl

@[simp] theorem cost_log (x : Num ℝ) :
    (log x : Charged κ κₛ (Num ℝ)).cost = CostVec.one (realOpcode κ .log) := rfl

@[simp] theorem get_root (u : Num ℝ) (k : Num ℕ) :
    (root u k : Charged κ κₛ (Num ℝ)).val.get = u.get ^ ((k.get : ℝ)⁻¹) := rfl

@[simp] theorem cost_root (u : Num ℝ) (k : Num ℕ) :
    (root u k : Charged κ κₛ (Num ℝ)).cost = CostVec.one (realOpcode κ .root) := rfl

end Arlib.Computation.Num
