import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Types
import FormalModelTheory.ForMathlib.Structure

open Cardinal
open FirstOrder
open Language
open Structure

universe u v w
variable {L : Language.{u, v}}
variable (T : L.Theory)

namespace Cardinal

def categorical (κ : Cardinal.{w}) : Prop :=
  ∀ {M N : Type w} [Nonempty M] [L.Structure M] [M ⊨ T]
  [Nonempty N] [L.Structure N] [N ⊨ T],
  #M = κ → #N = κ → Nonempty (M ≃[L] N)

end Cardinal

namespace FirstOrder.Language.Theory

def categorical (κ : Cardinal.{w}) : Prop := κ.categorical T

theorem categorical_of_saturated
    (κ : Cardinal.{w})
    (h : ∀ (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T], #M = κ → saturated T M) :
    T.categorical κ := by
  unfold categorical Cardinal.categorical
  intros
  apply iso_of_mk_eq_mk_of_saturated T <;> simp only [*]

theorem aleph0_categorical_of_saturated
    (h : ∀ (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T], #M = ℵ₀ → saturated T M) :
    categorical.{u, v, w} T ℵ₀ := by
  apply categorical_of_saturated.{u, v, w} T ℵ₀
  exact h

theorem aleph0_categorical_of_countably_saturated
    (h : ∀ (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T], #M = ℵ₀ → countably_saturated T M) :
    categorical.{u, v, w} T ℵ₀ := by
  unfold categorical Cardinal.categorical
  intros
  apply iso_of_countably_saturated T <;> simp only [*]

end FirstOrder.Language.Theory
