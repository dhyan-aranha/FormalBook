/-
Copyright 2022 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Moritz Firsching
-/
import Mathlib.Data.Matrix.DoublyStochastic
import Mathlib.Data.Real.Basic
/-!
# Van der Waerden's permanent conjecture

## TODO
  - statement
    - proof
  - Gurvits' Proposition
  - proof
    - Claim 1
    - Claim 2
  - Lemma 1
    - proof
  - Lemma 2
    - proof
  - Proof of Gurvits' Proposition
    - Case 1
    - Case 2
    - Claim
  - Farkas Lemma
-/



open Equiv
namespace Matrix

variable {n : ℕ}

def per (M : Matrix (Fin n) (Fin n) ℝ) := ∑ σ : Perm (Fin n), ∏ i, M (σ i) i

theorem permanent_conjecture (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ doublyStochastic ℝ (Fin n) → per M ≥ (n.factorial)/(n ^ n) := sorry
