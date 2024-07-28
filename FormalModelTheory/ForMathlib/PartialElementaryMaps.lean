import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

open Cardinal
open FirstOrder
open Function.Embedding

universe u v w

variable {L : Language.{u, v}}
variable (M : Type w) [L.Structure M]
variable (N : Type w) [L.Structure N]

structure PartialElementaryMap where
  domain : Set M
  codomain : Set N
  toFun : domain ≃ codomain
  map_formula :
    ∀ φ : L.Formula (domain),
    φ.Realize (M := M) (subtype domain) ↔
    φ.Realize (M := N) ((subtype codomain) ∘ toFun)
