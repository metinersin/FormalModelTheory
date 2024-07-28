import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Types
-- import Mathlib.ModelTheory.Syntax
-- import Mathlib.ModelTheory.Bundled

open Cardinal
open FirstOrder

universe u u' v v' w w'
variable {L : Language.{u, v}}
variable (T : L.Theory)
variable (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T]
variable (N : Type w) [Nonempty N] [L.Structure N] [N ⊨ T]

namespace Cardinal

def saturated (κ : Cardinal.{w}): Prop :=
  ∀ {α : Type w}, #α < κ → ∀ p : T.CompleteType α, p ∈ T.realizedTypes M α

end Cardinal

namespace FirstOrder.Language.Structure

def saturated : Prop := (#M).saturated T M

theorem iso_of_mk_eq_mk_of_saturated :
    saturated T M → saturated T N → #M = #N → Nonempty (M ≃[L] N) := by
  sorry

def countably_saturated : Prop := #M = ℵ₀ ∧ saturated T M

lemma saturated_iff_countably_saturated_of_mk_eq_aleph0 (h : #M = ℵ₀) :
    saturated T M ↔ countably_saturated T M := by
  unfold countably_saturated
  simp only [h, true_and]

theorem iso_of_countably_saturated :
    countably_saturated T M → countably_saturated T N → Nonempty (M ≃[L] N) := by
  rintro ⟨hM₁, hM₂⟩ ⟨hN₁, hN₂⟩
  have : #M = #N := by rw [hM₁, hN₁]
  apply iso_of_mk_eq_mk_of_saturated T M N <;> assumption

end FirstOrder.Language.Structure
