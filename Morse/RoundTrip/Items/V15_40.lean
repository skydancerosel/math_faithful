import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_40

namespace RoundTrip.V15_40

/-- The project's statement (universe instantiated at `0`): for `IsAnticommFamily J (k + 1)`,
`k = 2, 6`, and `2 ≤ (n/m_{k+1} − |c|)/4`: (i) every path in `Ω^{(c)}` (project path space of the
stratum of `J_k`) is joined to `φ(J')` for some `J' ∈ Ω_{k+1}(n)`; (ii) for `φ(J') ∈ Ω^{(c)}`,
`J'`, `J''` are joined in `Ω_{k+1}(n)` iff `φ(J')`, `φ(J'')` are joined. -/
def A : Prop := type_of% @Morse.theorem_24_5_pi0_two_six.{0}

theorem A_holds : A := @Morse.theorem_24_5_pi0_two_six.{0}

/-! ### B ⇒ A, only vacuously

A is a finite-stage statement in the project's path space (with the explicit range
`2 ≤ (n/m_{k+1} − |c|)/4`); B's first claim says nothing about `φ` and its second is about the
direct limit, from which no finite-stage statement follows. A is re-proved outright: the
project's proof is copied verbatim (it uses only non-item lemmas: the clopen version of Theorem
22.1, `isClopen_omegaComp`, `omega_hidx_two`, the homotopy equivalence `φ ≃ minPaths`). -/

section Outright
open Morse
open Matrix Set Function Topology
open scoped unitInterval Morse.MatrixInner

section Pi0

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}
  (hJ : IsAnticommFamily J (k + 1))
include hJ

/-- **The `π₀` part of Theorem 24.5 at the finite stage, `k = 2, 6`** (Milnor pp. 147–148):
for `(n/m_{k+1} − |c|)/4 ≥ 2`, (i) every path in `Ω^{(c)}` is joined, in
`Ω(Ω_k(n); J_k, −J_k)`, to `φ_r(J')` for some `J' ∈ Ω_{k+1}(n)`; (ii) for `φ_r(J') ∈ Ω^{(c)}`,
`J'` and `J''` are joined in `Ω_{k+1}(n)` iff `φ_r(J')` and `φ_r(J'')` are joined.  With
`Morse.exists_mem_omegaComp_two`, `Morse.exists_mem_omegaComp_six` and
`Morse.disjoint_omegaComp` (every path lies in exactly one `Ω^{(c)}`), `φ_r` thus identifies
`π₀Ω_{k+1}(n)^{(c)}` with `π₀Ω^{(c)}` for every `c` in this range. -/
theorem theorem_24_5_pi0_two_six' (hk : k = 2 ∨ k = 6) (c : ℤ)
    (hc : 2 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4) :
    (∀ ω ∈ omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2),
      ∃ J' : Omega J (k + 1), Joined (omegaPhi hJ J' : PathSp _ _ _) ω) ∧
    ∀ J' J'' : Omega J (k + 1), (omegaPhi hJ J' : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) →
      (Joined J' J'' ↔ Joined (omegaPhi hJ J' : PathSp _ _ _) (omegaPhi hJ J'')) := by
  have hk0 : k ≠ 0 := by omega
  have hii := isCentralI_iWordM hJ hk
  set Ω' := omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) with hΩ'_def
  have hΩ' : IsClopen Ω' := isClopen_omegaComp (hJ.mono k.le_succ) hk0 hii _
  have hpush0 := pushesInto_cube_clopen
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    hΩ' (omega_hidx_two hJ hk0 (by omega) (by omega) hii c)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    (K := Fin 0) (by simpa using hc)
  have hpush1 := pushesInto_cyl_clopen
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    hΩ' (omega_hidx_two hJ hk0 (by omega) (by omega) hii c)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    (K := Fin 0) (by simpa using hc)
  obtain ⟨e, he⟩ := isHomotopyEquiv_omegaPhi_minPaths hJ
  have hφ : ∀ x, (omegaPhi hJ x : PathSp _ _ _) = ((e.toFun x : minPaths _ _ _) : PathSp _ _ _) :=
    fun x => (congrFun (congrArg DFunLike.coe he) x).symm
  let z : I^(Fin 0) := fun i => i.elim0
  refine ⟨fun ω hω => ?_, fun J' J'' hJ' => ⟨fun h => h.map (omegaPhi hJ).continuous, ?_⟩⟩
  · -- (i) push `ω` into the minimal geodesics
    obtain ⟨h', hh', ⟨H⟩⟩ := hpush0 (ContinuousMap.const _ ω) fun _ => hω
    let γ : minPaths _ _ _ := ⟨h' z, (hh' z).1⟩
    refine ⟨e.invFun γ, ?_⟩
    rw [hφ]
    exact ((joined_homotopyEquiv e (e.invFun γ) γ).1.map continuous_subtype_val).trans
      ⟨(H.evalAt z).symm⟩
  · -- (ii) push a path between `φ J'` and `φ J''` into the minimal geodesics
    rintro ⟨P⟩
    have hPΩ : ∀ t, P t ∈ Ω' := fun t =>
      (isConnected_range P.continuous).isPreconnected.subset_isClopen hΩ'
        ⟨_, ⟨0, rfl⟩, by rw [P.source]; exact hJ'⟩ ⟨t, rfl⟩
    let h : C(I × I^(Fin 0), PathSp _ _ _) := ⟨fun q => P q.1, by fun_prop⟩
    obtain ⟨h', hh', ⟨H⟩⟩ := hpush1 h fun q => hPΩ q.1
    have hmin : ∀ x : Omega J (k + 1), (omegaPhi hJ x : PathSp _ _ _) ∈ minPaths _ _ _ :=
      fun x => by rw [hφ]; exact (e.toFun x).2
    have h0 : h' (0, z) = omegaPhi hJ J' := by
      rw [← H.fst_eq_snd (show (0, z) ∈ h ⁻¹' (minPaths _ _ _ ∩ Ω') from
        ⟨by simp [h, hmin], by simp [h, hJ']⟩)]
      simp [h]
    have h1 : h' (1, z) = omegaPhi hJ J'' := by
      rw [← H.fst_eq_snd (show (1, z) ∈ h ⁻¹' (minPaths _ _ _ ∩ Ω') from
        ⟨by simp [h, hmin], by simpa [h] using hPΩ 1⟩)]
      simp [h]
    let Q : Path (e.toFun J') (e.toFun J'') :=
      { toFun := fun t => ⟨h' (t, z), (hh' (t, z)).1⟩
        continuous_toFun := by fun_prop
        source' := Subtype.ext (by change h' (0, z) = _; rw [h0, hφ])
        target' := Subtype.ext (by change h' (1, z) = _; rw [h1, hφ]) }
    exact ((joined_homotopyEquiv e J' (e.toFun J')).2.symm.trans
      (Joined.map (⟨Q⟩ : Joined (e.toFun J') (e.toFun J'')) e.invFun.continuous)).trans
      (joined_homotopyEquiv e J'' (e.toFun J'')).2

end Pi0

end Outright

theorem B_to_A : B → A := fun _ => @theorem_24_5_pi0_two_six'

#rt_check RoundTrip.V15_40.B_to_A [Morse.theorem_24_5_pi0_two_six]
#rt_overlap RoundTrip.V15_40.B_to_A [Morse.theorem_24_5_pi0_two_six]

end RoundTrip.V15_40
