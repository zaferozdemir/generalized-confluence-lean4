module

public import Mathlib

@[expose] public section

namespace GeneralizedConfluence

def relPow {W : Type} (R : W → W → Prop) :
    Nat → W → W → Prop
  | 0, x, y => x = y
  | n + 1, x, y =>
      ∃ z, R x z ∧ relPow R n z y

def boxN {W : Type} (R : W → W → Prop)
    (n : Nat) (P : W → Prop) (w : W) : Prop :=
  ∀ v, relPow R n w v → P v

def diamondN {W : Type} (R : W → W → Prop)
    (n : Nat) (P : W → Prop) (w : W) : Prop :=
  ∃ v, relPow R n w v ∧ P v

def box {W : Type} (R : W → W → Prop)
    (P : W → Prop) (w : W) : Prop :=
  ∀ v, R w v → P v

def diamond {W : Type} (R : W → W → Prop)
    (P : W → Prop) (w : W) : Prop :=
  ∃ v, R w v ∧ P v

def confluent {W : Type} (R : W → W → Prop)
    (m n : Nat) : Prop :=
  ∀ w v u, R w v → R w u →
    ∃ x, relPow R m v x ∧ relPow R n u x

def frameValid {W : Type} (R : W → W → Prop)
    (m n : Nat) : Prop :=
  ∀ (P : W → Prop) (w : W),
    diamond R (boxN R m P) w →
    box R (diamondN R n P) w

theorem generalized_confluence_correspondence
    {W : Type} (R : W → W → Prop) (m n : Nat) :
    frameValid R m n ↔ confluent R m n := by
  constructor
  · intro hValid w v u hwv hwu
    let P : W → Prop := fun x => relPow R m v x
    have hvBox : boxN R m P v := by
      intro y hy
      exact hy
    have hAnt : diamond R (boxN R m P) w := by
      exact ⟨v, hwv, hvBox⟩
    have hCons := hValid P w hAnt
    have huDiamond := hCons u hwu
    rcases huDiamond with ⟨x, hux, hvx⟩
    exact ⟨x, hvx, hux⟩
  · intro hConf P w hAnt
    rcases hAnt with ⟨v, hwv, hvBox⟩
    intro u hwu
    obtain ⟨x, hvx, hux⟩ :=
      hConf w v u hwv hwu
    exact ⟨x, hux, hvBox x hvx⟩
    
/- Basic properties of relation powers. -/

theorem relPow_zero_iff
    {W : Type} (R : W → W → Prop) (x y : W) :
    relPow R 0 x y ↔ x = y := by
  rfl

theorem relPow_succ_iff
    {W : Type} (R : W → W → Prop)
    (n : Nat) (x y : W) :
    relPow R (n + 1) x y ↔
      ∃ z, R x z ∧ relPow R n z y := by
  rfl

theorem relPow_one_iff
    {W : Type} (R : W → W → Prop) (x y : W) :
    relPow R 1 x y ↔ R x y := by
  simp [relPow]

theorem relPow_two_iff
    {W : Type} (R : W → W → Prop) (x y : W) :
    relPow R 2 x y ↔
      ∃ z, R x z ∧ R z y := by
  simp [relPow]

/- Zero-step modal operators. -/

theorem boxN_zero_iff
    {W : Type} (R : W → W → Prop)
    (P : W → Prop) (w : W) :
    boxN R 0 P w ↔ P w := by
  simp [boxN, relPow]

theorem diamondN_zero_iff
    {W : Type} (R : W → W → Prop)
    (P : W → Prop) (w : W) :
    diamondN R 0 P w ↔ P w := by
  simp [diamondN, relPow]

/- The ordinary confluence instance. -/

theorem ordinary_confluence_correspondence
    {W : Type} (R : W → W → Prop) :
    frameValid R 1 1 ↔ confluent R 1 1 :=
  generalized_confluence_correspondence R 1 1


/- Composition property of relation powers. -/


theorem relPow_add_iff
    {W : Type} (R : W → W → Prop)
    (m n : Nat) (x z : W) :
    relPow R (m + n) x z ↔
      ∃ y, relPow R m x y ∧ relPow R n y z := by
  induction m generalizing x z with
  | zero =>
      simp [relPow]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [relPow]
      constructor
      · intro h
        obtain ⟨a, hxa, haz⟩ := h
        obtain ⟨y, hay, hyz⟩ := (ih a z).mp haz
        exact ⟨y, ⟨a, hxa, hay⟩, hyz⟩
      · intro h
        obtain ⟨y, hay, hyz⟩ := h
        obtain ⟨a, hxa, hay'⟩ := hay
        exact ⟨a, hxa, (ih a z).mpr ⟨y, hay', hyz⟩⟩

theorem relPow_mono
    {W : Type} {R S : W → W → Prop}
    (hRS : ∀ x y, R x y → S x y)
    (n : Nat) (x y : W) :
    relPow R n x y → relPow S n x y := by
  induction n generalizing x y with
  | zero =>
      simp [relPow]
  | succ n ih =>
      intro h
      simp only [relPow] at h ⊢
      obtain ⟨z, hxz, hzy⟩ := h
      exact ⟨z, hRS x z hxz, ih z y hzy⟩

theorem relPow_transitive
    {W : Type} {R : W → W → Prop}
    (hTrans : ∀ x y z, R x y → R y z → R x z)
    (n : Nat) (x y : W) :
    relPow R (n + 1) x y → R x y := by
  induction n generalizing x y with
  | zero =>
      intro h
      simpa [relPow] using h
  | succ n ih =>
      intro h
      simp only [relPow] at h
      obtain ⟨z, hxz, hzy⟩ := h
      exact hTrans x z y hxz (ih z y hzy)






theorem relPow_symmetric
    {W : Type} {R : W → W → Prop}
    (hSymm : ∀ x y, R x y → R y x)
    (n : Nat) (x y : W) :
    relPow R n x y → relPow R n y x := by
  induction n generalizing x y with
  | zero =>
      intro h
      simpa [relPow] using h.symm
  | succ n ih =>
      intro h
      simp only [relPow] at h
      obtain ⟨z, hxz, hzy⟩ := h
      have hyz : relPow R n y z :=
        ih z y hzy
      have hzx : R z x :=
        hSymm x z hxz
      exact (relPow_add_iff R n 1 y x).mpr
        ⟨z, hyz, (relPow_one_iff R z x).mpr hzx⟩


def relUnion {W : Type}
    (R S : W → W → Prop) : W → W → Prop :=
  fun x y => R x y ∨ S x y


theorem relPow_union_mono
    {W : Type} (R S T : W → W → Prop)
    (hR : ∀ x y, R x y → T x y)
    (hS : ∀ x y, S x y → T x y)
    (n : Nat) (x y : W) :
    relPow (relUnion R S) n x y →
      relPow T n x y := by
  apply relPow_mono
  · intro a b hab
    exact hab.elim (hR a b) (hS a b)



theorem confluent_zero_right_iff
    {W : Type} (R : W → W → Prop) (m : Nat) :
    confluent R m 0 ↔
      ∀ w v u, R w v → R w u → relPow R m v u := by
  constructor
  · intro h w v u hwv hwu
    obtain ⟨x, hvx, hux⟩ := h w v u hwv hwu
    have hx : x = u := by
      simpa [relPow] using hux.symm
    subst x
    exact hvx
  · intro h w v u hwv hwu
    exact ⟨u, h w v u hwv hwu, by simp [relPow]⟩



def ordinaryConfluent {W : Type}
    (R : W → W → Prop) : Prop :=
  ∀ w v u, R w v → R w u →
    ∃ x, R v x ∧ R u x

theorem ordinary_confluent_iff_generalized
    {W : Type} (R : W → W → Prop) :
    ordinaryConfluent R ↔ confluent R 1 1 := by
  unfold ordinaryConfluent confluent
  constructor
  · intro h w v u hwv hwu
    obtain ⟨x, hvx, hux⟩ := h w v u hwv hwu
    exact ⟨x, by simpa [relPow] using hvx,
      by simpa [relPow] using hux⟩
  · intro h w v u hwv hwu
    obtain ⟨x, hvx, hux⟩ := h w v u hwv hwu
    exact ⟨x, by simpa [relPow] using hvx,
      by simpa [relPow] using hux⟩

theorem frameValid_implies_confluent
    {W : Type} (R : W → W → Prop)
    (m n : Nat) :
    frameValid R m n → confluent R m n := by
  exact (generalized_confluence_correspondence R m n).mp

theorem confluent_implies_frameValid
    {W : Type} (R : W → W → Prop)
    (m n : Nat) :
    confluent R m n → frameValid R m n := by
  exact (generalized_confluence_correspondence R m n).mpr


def sampleRelation : Fin 3 → Fin 3 → Prop :=
  fun x y => (x = 0 ∧ y = 1) ∨
             (x = 0 ∧ y = 2) ∨
             (x = 1 ∧ y = 2)

theorem sampleRelation_not_confluent :
    ¬ confluent sampleRelation 1 1 := by
  intro h
  have h01 : sampleRelation 0 1 := by
    simp [sampleRelation]
  have h02 : sampleRelation 0 2 := by
    simp [sampleRelation]
  obtain ⟨x, h1x, h2x⟩ := h 0 1 2 h01 h02
  have h2x' : sampleRelation 2 x :=
    (relPow_one_iff sampleRelation 2 x).mp h2x
  simp [sampleRelation] at h2x'


def completeRelation : Fin 3 → Fin 3 → Prop :=
  fun x y => x ≠ y


theorem completeRelation_symmetric :
    ∀ x y, completeRelation x y →
      completeRelation y x := by
  intro x y h
  exact Ne.symm h


theorem completeRelation_confluent :
    confluent completeRelation 1 1 := by
  intro w v u hwv hwu
  exact ⟨w,
    (relPow_one_iff completeRelation v w).mpr (Ne.symm hwv),
    (relPow_one_iff completeRelation u w).mpr (Ne.symm hwu)⟩

theorem completeRelation_frameValid :
    frameValid completeRelation 1 1 := by
  exact (generalized_confluence_correspondence
    completeRelation 1 1).mpr completeRelation_confluent

theorem sampleRelation_not_frameValid :
    ¬ frameValid sampleRelation 1 1 := by
  intro h
  apply sampleRelation_not_confluent
  exact (generalized_confluence_correspondence
    sampleRelation 1 1).mp h


theorem completeRelation_not_confluent_zero_zero :
    ¬ confluent completeRelation 0 0 := by
  intro h
  have h01 : completeRelation (0 : Fin 3) 1 := by
    simp [completeRelation]
  have h02 : completeRelation (0 : Fin 3) 2 := by
    simp [completeRelation]
  obtain ⟨x, hx1, hx2⟩ := h 0 1 2 h01 h02
  have hx1' : x = 1 := by
    exact (show 1 = x by simpa [relPow] using hx1).symm
  have hx2' : x = 2 := by
    exact (show 2 = x by simpa [relPow] using hx2).symm
  have h12 : (1 : Fin 3) = 2 :=
    hx1'.symm.trans hx2'
  exact (by decide : (1 : Fin 3) ≠ 2) h12



def singletonRelation : Fin 1 → Fin 1 → Prop :=
  fun _ _ => True


theorem singleton_relPow
    (n : Nat) (x y : Fin 1) :
    relPow singletonRelation n x y := by
  induction n with
  | zero =>
      exact Subsingleton.elim x y
  | succ n ih =>
      exact ⟨x, True.intro, ih⟩


theorem singleton_confluent_all :
    ∀ m n : Nat, confluent singletonRelation m n := by
  intro m n w v u hwv hwu
  exact ⟨v,
    singleton_relPow m v v,
    singleton_relPow n u v⟩


theorem singleton_frameValid_all :
    ∀ m n : Nat, frameValid singletonRelation m n := by
  intro m n
  exact (generalized_confluence_correspondence
    singletonRelation m n).mpr
      (singleton_confluent_all m n)

theorem completeRelation_not_confluent_zero_one :
    ¬ confluent completeRelation 0 1 := by
  intro h
  have h01 : completeRelation (0 : Fin 3) 1 := by
    simp [completeRelation]
  obtain ⟨x, hx0, hx1⟩ := h 0 1 1 h01 h01
  have hx : (1 : Fin 3) = x := by
    simpa [relPow] using hx0
  have hrel : completeRelation (1 : Fin 3) x :=
    (relPow_one_iff completeRelation 1 x).mp hx1
  subst x
  simp [completeRelation] at hrel

theorem completeRelation_not_confluent_one_zero :
    ¬ confluent completeRelation 1 0 := by
  intro h
  have h01 : completeRelation (0 : Fin 3) 1 := by
    simp [completeRelation]
  obtain ⟨x, hx1, hx0⟩ := h 0 1 1 h01 h01
  have hx : x = 1 := Eq.symm (by
    simpa [relPow] using hx0)
  have hrel : completeRelation 1 1 := by
    have hrelx : completeRelation 1 x :=
      (relPow_one_iff completeRelation 1 x).mp hx1
    rw [hx] at hrelx
    exact hrelx
  exact (by simp [completeRelation] : ¬ completeRelation 1 1) hrel

theorem completeRelation_has_other
    (x : Fin 3) :
    ∃ z : Fin 3, completeRelation x z := by
  by_cases hx : x = 0
  · refine ⟨1, ?_⟩
    simp [completeRelation, hx]
  · refine ⟨0, ?_⟩
    change x ≠ 0
    exact hx

example (x : Fin 3) : ∃ z : Fin 3, z ≠ x := by
  cases x using Fin.cases with
  | zero =>
      exact ⟨1, by decide⟩
  | succ y =>
      cases y using Fin.cases with
      | zero =>
          exact ⟨0, by decide⟩
      | succ z =>
          have hz : z = 0 := Subsingleton.elim z 0
          subst z
          exact ⟨0, by decide⟩

theorem completeRelation_has_common_other
    (x y : Fin 3) :
    ∃ z : Fin 3, z ≠ x ∧ z ≠ y := by
  cases x using Fin.cases with
  | zero =>
      cases y using Fin.cases with
      | zero =>
          exact ⟨1, by decide⟩
      | succ y =>
          cases y using Fin.cases with
          | zero =>
              exact ⟨2, by decide⟩
          | succ z =>
              have hz : z = 0 := Subsingleton.elim z 0
              subst z
              exact ⟨1, by decide⟩
  | succ x =>
      cases x using Fin.cases with
      | zero =>
          cases y using Fin.cases with
          | zero =>
              exact ⟨2, by decide⟩
          | succ y =>
              cases y using Fin.cases with
              | zero =>
                  exact ⟨0, by decide⟩
              | succ z =>
                  have hz : z = 0 := Subsingleton.elim z 0
                  subst z
                  exact ⟨0, by decide⟩
      | succ x =>
          have hx : x = 0 := Subsingleton.elim x 0
          subst x
          cases y using Fin.cases with
          | zero =>
              exact ⟨1, by decide⟩
          | succ y =>
              cases y using Fin.cases with
              | zero =>
                  exact ⟨0, by decide⟩
              | succ z =>
                  have hz : z = 0 := Subsingleton.elim z 0
                  subst z
                  exact ⟨0, by decide⟩

theorem completeRelation_relPow_two
    (x y : Fin 3) :
    relPow completeRelation 2 x y := by
  obtain ⟨z, hzx, hzy⟩ :=
    completeRelation_has_common_other x y
  have hxz : completeRelation x z := by
    exact Ne.symm hzx
  have hzy' : completeRelation z y := by
    exact hzy
  exact ⟨z, hxz,
    (relPow_one_iff completeRelation z y).mpr hzy'⟩

theorem completeRelation_relPow_two_check
    (x y : Fin 3) :
    ∃ z : Fin 3,
      completeRelation x z ∧ completeRelation z y := by
  simpa [relPow] using completeRelation_relPow_two x y


theorem completeRelation_relPow_three_iff
    (x y : Fin 3) :
    relPow completeRelation 3 x y ↔
      ∃ a b : Fin 3,
        completeRelation x a ∧
        completeRelation a b ∧
        completeRelation b y := by
  constructor
  · intro h
    simp only [relPow] at h
    obtain ⟨a, hab, b, hbc, c, hcd, hcy⟩ := h
    subst c
    exact ⟨a, b, hab, hbc, hcd⟩
  · rintro ⟨a, b, hab, hbc, hcd⟩
    simp only [relPow]
    exact ⟨a, hab, b, hbc, y, hcd, rfl⟩

theorem completeRelation_relPow_three
    (x y : Fin 3) :
    relPow completeRelation 3 x y := by
  apply (completeRelation_relPow_three_iff x y).mpr
  obtain ⟨a, hax, hay⟩ :=
    completeRelation_has_common_other x y
  have hxa : completeRelation x a :=
    Ne.symm hax
  have hay' : completeRelation a y := hay
  obtain ⟨b, hba, hby⟩ :=
    completeRelation_has_common_other a y
  have hab : completeRelation a b :=
    Ne.symm hba
  have hby' : completeRelation b y := hby
  exact ⟨a, b, hxa, hab, hby'⟩
theorem completeRelation_relPow_four
    (x y : Fin 3) :
    relPow completeRelation 4 x y := by
  apply (relPow_succ_iff completeRelation 3 x y).mpr
  obtain ⟨z, hzx, hzy⟩ :=
    completeRelation_has_common_other x y
  have hxz : completeRelation x z :=
    Ne.symm hzx
  have hzy' : completeRelation z y := hzy
  obtain ⟨u, hzu, huy⟩ :=
    completeRelation_has_common_other z y
  have hzu' : completeRelation z u :=
    Ne.symm hzu
  have huy' : completeRelation u y := huy
  exact ⟨z, hxz,
    (completeRelation_relPow_three z y)⟩

theorem completeRelation_relPow_ge_two
    (n : Nat) (x y : Fin 3) :
    relPow completeRelation (n + 2) x y := by
  induction n generalizing x y with
  | zero =>
      exact completeRelation_relPow_two x y
  | succ n ih =>
      obtain ⟨z, hxz⟩ :=
        completeRelation_has_other x
      exact ⟨z, hxz, ih z y⟩

theorem completeRelation_confluent_zero_ge_two
    (n : Nat) :
    confluent completeRelation 0 (n + 2) := by
  intro w v u hwv hwu
  exact ⟨v,
    (relPow_zero_iff completeRelation v v).mpr rfl,
    completeRelation_relPow_ge_two n u v⟩

theorem completeRelation_confluent_ge_two_zero
    (n : Nat) :
    confluent completeRelation (n + 2) 0 := by
  intro w v u hwv hwu
  exact ⟨u,
    completeRelation_relPow_ge_two n v u,
    (relPow_zero_iff completeRelation u u).mpr rfl⟩

theorem completeRelation_confluent_ge_two_ge_two
    (m n : Nat) :
    confluent completeRelation (m + 2) (n + 2) := by
  intro w v u hwv hwu
  exact ⟨w,
    completeRelation_relPow_ge_two m v w,
    completeRelation_relPow_ge_two n u w⟩

theorem completeRelation_confluent_one_ge_two
    (n : Nat) :
    confluent completeRelation 1 (n + 2) := by
  intro w v u hwv hwu
  exact ⟨w,
    (relPow_one_iff completeRelation v w).mpr
      (Ne.symm hwv),
    completeRelation_relPow_ge_two n u w⟩

theorem completeRelation_confluent_ge_two_one
    (n : Nat) :
    confluent completeRelation (n + 2) 1 := by
  intro w v u hwv hwu
  exact ⟨w,
    completeRelation_relPow_ge_two n v w,
    (relPow_one_iff completeRelation u w).mpr
      (Ne.symm hwu)⟩

theorem completeRelation_confluent_classification
    (m n : Nat)
    (h : m + n ≥ 2) :
    confluent completeRelation m n := by
  cases m with
  | zero =>
    cases n with
    | zero => simp at h
    | succ n =>
      cases n with
      | zero => simp at h
      | succ n =>
        exact completeRelation_confluent_zero_ge_two n
  | succ m =>
    cases m with
    | zero =>
      cases n with
      | zero => simp at h
      | succ n =>
        cases n with
        | zero =>
          exact completeRelation_confluent
        | succ n =>
          exact completeRelation_confluent_one_ge_two n
    | succ m =>
      cases n with
      | zero =>
        exact completeRelation_confluent_ge_two_zero m
      | succ n =>
        cases n with
        | zero =>
          exact completeRelation_confluent_ge_two_one m
        | succ n =>
          exact completeRelation_confluent_ge_two_ge_two m n

theorem completeRelation_frameValid_classification
    (m n : Nat)
    (h : m + n ≥ 2) :
    frameValid completeRelation m n := by
  exact (generalized_confluence_correspondence
    completeRelation m n).mpr
      (completeRelation_confluent_classification m n h)

theorem completeRelation_not_confluent_below_two
    (m n : Nat)
    (h : m + n < 2) :
    ¬ confluent completeRelation m n := by
  cases m with
  | zero =>
    cases n with
    | zero =>
      exact completeRelation_not_confluent_zero_zero
    | succ n =>
      cases n with
      | zero =>
        exact completeRelation_not_confluent_zero_one
      | succ n =>
        omega
  | succ m =>
    cases m with
    | zero =>
      cases n with
      | zero =>
        exact completeRelation_not_confluent_one_zero
      | succ n =>
        omega
    | succ m =>
      omega

theorem completeRelation_confluent_iff
    (m n : Nat) :
    confluent completeRelation m n ↔ m + n ≥ 2 := by
  constructor
  · intro hConf
    by_cases hlt : m + n < 2
    · exact False.elim
        ((completeRelation_not_confluent_below_two m n hlt) hConf)
    · exact Nat.le_of_not_gt hlt
  · intro hmn
    exact completeRelation_confluent_classification m n hmn

theorem completeRelation_frameValid_iff
    (m n : Nat) :
    frameValid completeRelation m n ↔ m + n ≥ 2 := by
  rw [generalized_confluence_correspondence]
  exact completeRelation_confluent_iff m n

theorem completeRelation_irreflexive :
    ∀ x : Fin 3, ¬ completeRelation x x := by
  intro x
  simp [completeRelation]

theorem completeRelation_connected :
    ∀ x y : Fin 3, x ≠ y →
      completeRelation x y := by
  intro x y hxy
  exact hxy
theorem completeRelation_diameter_two :
    ∀ x y : Fin 3,
      relPow completeRelation 2 x y := by
  intro x y
  exact completeRelation_relPow_two x y

def twoPointRelation : Fin 2 → Fin 2 → Prop :=
  fun x y => x ≠ y

theorem twoPointRelation_symmetric :
    ∀ x y : Fin 2,
      twoPointRelation x y →
      twoPointRelation y x := by
  intro x y h
  exact Ne.symm h

theorem twoPointRelation_irreflexive :
    ∀ x : Fin 2,
      ¬ twoPointRelation x x := by
  intro x
  simp [twoPointRelation]

theorem twoPointRelation_not_all_two_step :
    ¬ ∀ x y : Fin 2,
      relPow twoPointRelation 2 x y := by
  intro h
  have h01 := h 0 1
  simp [relPow, twoPointRelation] at h01

theorem twoPointRelation_relPow_two_iff
    (x y : Fin 2) :
    relPow twoPointRelation 2 x y ↔ x = y := by
  cases x using Fin.cases with
  | zero =>
    cases y using Fin.cases with
    | zero =>
      simp [relPow, twoPointRelation]
    | succ y =>
      have hy : y = 0 := Subsingleton.elim y 0
      subst y
      simp [relPow, twoPointRelation]
  | succ x =>
    have hx : x = 0 := Subsingleton.elim x 0
    subst x
    cases y using Fin.cases with
    | zero =>
      simp [relPow, twoPointRelation]
    | succ y =>
      have hy : y = 0 := Subsingleton.elim y 0
      subst y
      simp [relPow, twoPointRelation]

theorem twoPointRelation_confluent_one_one :
    confluent twoPointRelation 1 1 := by
  intro w v u hwv hwu
  cases v using Fin.cases with
  | zero =>
    cases u using Fin.cases with
    | zero =>
      exact ⟨1, by simp [relPow, twoPointRelation],
        by simp [relPow, twoPointRelation]⟩
    | succ u =>
      have hu : u = 0 := Subsingleton.elim u 0
      subst u
      cases w using Fin.cases with
      | zero =>
        simp [twoPointRelation] at hwv
      | succ w =>
        have hw : w = 0 := Subsingleton.elim w 0
        subst w
        simp [twoPointRelation] at hwu
  | succ v =>
    have hv : v = 0 := Subsingleton.elim v 0
    subst v
    cases u using Fin.cases with
    | zero =>
      cases w using Fin.cases with
      | zero =>
        simp [twoPointRelation] at hwu
      | succ w =>
        have hw : w = 0 := Subsingleton.elim w 0
        subst w
        simp [twoPointRelation] at hwv
    | succ u =>
      have hu : u = 0 := Subsingleton.elim u 0
      subst u
      exact ⟨0, by simp [relPow, twoPointRelation],
        by simp [relPow, twoPointRelation]⟩


theorem twoPointRelation_frameValid_one_one :
    frameValid twoPointRelation 1 1 := by
  exact (generalized_confluence_correspondence
    twoPointRelation 1 1).mpr
      twoPointRelation_confluent_one_one

theorem twoPointRelation_confluent_zero_zero :
    confluent twoPointRelation 0 0 := by
  intro w v u hwv hwu
  have hvu : v = u := by
    cases w using Fin.cases with
    | zero =>
      cases v using Fin.cases with
      | zero =>
        exact False.elim (hwv rfl)
      | succ v =>
        cases u using Fin.cases with
        | zero =>
          exact False.elim (hwu rfl)
        | succ u =>
          congr 1
          exact Subsingleton.elim v u
    | succ w =>
      have hw : w = 0 := Subsingleton.elim w 0
      subst w
      cases v using Fin.cases with
      | zero =>
        cases u using Fin.cases with
        | zero =>
          rfl
        | succ u =>
          exact False.elim
            (hwu (congrArg Fin.succ
              (Subsingleton.elim (0 : Fin 1) u)))
      | succ v =>
        cases u using Fin.cases with
        | zero =>
          exact False.elim
            (hwv (congrArg Fin.succ
              (Subsingleton.elim (0 : Fin 1) v)))
        | succ u =>
          congr 1
          exact Subsingleton.elim v u
  refine ⟨v, ?_, ?_⟩
  · exact (relPow_zero_iff twoPointRelation v v).mpr rfl
  · exact (relPow_zero_iff twoPointRelation u v).mpr hvu.symm

theorem twoPointRelation_not_confluent_zero_one :
    ¬ confluent twoPointRelation 0 1 := by
  intro h
  have hwv : twoPointRelation (0 : Fin 2) 1 := by
    simp [twoPointRelation]
  obtain ⟨x, hx0, hx1⟩ := h 0 1 1 hwv hwv
  have hx : x = 1 := by
    exact ((relPow_zero_iff twoPointRelation 1 x).mp hx0).symm
  subst x
  have hrel : twoPointRelation 1 1 :=
    (relPow_one_iff twoPointRelation 1 1).mp hx1
  exact hrel rfl

theorem twoPointRelation_not_confluent_one_zero :
    ¬ confluent twoPointRelation 1 0 := by
  intro h
  have hwv : twoPointRelation (0 : Fin 2) 1 := by
    simp [twoPointRelation]
  obtain ⟨x, hx1, hx0⟩ := h 0 1 1 hwv hwv
  have hx : x = 1 := by
    exact ((relPow_zero_iff twoPointRelation 1 x).mp hx0).symm
  subst x
  have hrel : twoPointRelation 1 1 :=
    (relPow_one_iff twoPointRelation 1 1).mp hx1
  exact hrel rfl

theorem relPow_add
    {W : Type} (R : W → W → Prop)
    (m n : Nat) (x z : W) :
    relPow R (m + n) x z ↔
      ∃ y, relPow R m x y ∧ relPow R n y z :=
  relPow_add_iff R m n x z

theorem twoPointRelation_relPow_four_iff
    (x y : Fin 2) :
    relPow twoPointRelation 4 x y ↔ x = y := by
  change relPow twoPointRelation (2 + 2) x y ↔ x = y
  rw [relPow_add]
  constructor
  · rintro ⟨z, hxz, hzy⟩
    have h1 :=
      (twoPointRelation_relPow_two_iff x z).mp hxz
    have h2 :=
      (twoPointRelation_relPow_two_iff z y).mp hzy
    exact h1.trans h2
  · intro hxy
    subst y
    exact ⟨x,
      (twoPointRelation_relPow_two_iff x x).mpr rfl,
      (twoPointRelation_relPow_two_iff x x).mpr rfl⟩

theorem twoPointRelation_relPow_six_iff
    (x y : Fin 2) :
    relPow twoPointRelation 6 x y ↔ x = y := by
  change relPow twoPointRelation (4 + 2) x y ↔ x = y
  rw [relPow_add]
  constructor
  · rintro ⟨z, hxz, hzy⟩
    have h1 :=
      (twoPointRelation_relPow_four_iff x z).mp hxz
    have h2 :=
      (twoPointRelation_relPow_two_iff z y).mp hzy
    exact h1.trans h2
  · intro hxy
    subst y
    exact ⟨x,
      (twoPointRelation_relPow_four_iff x x).mpr rfl,
      (twoPointRelation_relPow_two_iff x x).mpr rfl⟩

theorem twoPointRelation_relPow_eight_iff
    (x y : Fin 2) :
    relPow twoPointRelation 8 x y ↔ x = y := by
  change relPow twoPointRelation (6 + 2) x y ↔ x = y
  rw [relPow_add]
  constructor
  · rintro ⟨z, hxz, hzy⟩
    have h1 :=
      (twoPointRelation_relPow_six_iff x z).mp hxz
    have h2 :=
      (twoPointRelation_relPow_two_iff z y).mp hzy
    exact h1.trans h2
  · intro hxy
    subst y
    exact ⟨x,
      (twoPointRelation_relPow_six_iff x x).mpr rfl,
      (twoPointRelation_relPow_two_iff x x).mpr rfl⟩

theorem twoPointRelation_even_step
    (k : Nat) (x y : Fin 2)
    (hk : ∀ a b : Fin 2,
      relPow twoPointRelation (2 * k) a b ↔ a = b) :
    relPow twoPointRelation (2 * (k + 1)) x y ↔ x = y := by
  have hdecomp :
      2 * (k + 1) = 2 * k + 2 := by omega
  rw [hdecomp]
  rw [relPow_add]
  constructor
  · rintro ⟨z, hxz, hzy⟩
    have h1 := (hk x z).mp hxz
    have h2 :=
      (twoPointRelation_relPow_two_iff z y).mp hzy
    exact h1.trans h2
  · intro hxy
    subst y
    exact ⟨x, (hk x x).mpr rfl,
      (twoPointRelation_relPow_two_iff x x).mpr rfl⟩

theorem twoPointRelation_even_relPow_iff
    (k : Nat) (x y : Fin 2) :
    relPow twoPointRelation (2 * k) x y ↔ x = y := by
  induction k generalizing x y with
  | zero =>
    exact relPow_zero_iff twoPointRelation x y
  | succ k ih =>
    apply twoPointRelation_even_step k x y
    intro a b
    exact ih a b

theorem twoPointRelation_odd_relPow_iff
    (k : Nat) (x y : Fin 2) :
    relPow twoPointRelation (2 * k + 1) x y ↔ x ≠ y := by
  have hdecomp : 2 * k + 1 = 1 + 2 * k := by omega
  rw [hdecomp, relPow_add]
  constructor
  · rintro ⟨z, hxz, hzy⟩
    have hzy' :=
      (twoPointRelation_even_relPow_iff k z y).mp hzy
    subst y
    exact (relPow_one_iff twoPointRelation x z).mp hxz
  · intro hxy
    exact ⟨y,
      (relPow_one_iff twoPointRelation x y).mpr hxy,
      (twoPointRelation_even_relPow_iff k y y).mpr rfl⟩

theorem twoPointRelation_confluent_even_even
    (k l : Nat) :
    confluent twoPointRelation (2 * k) (2 * l) := by
  intro w v u hwv hwu
  obtain ⟨x, hxv, hxu⟩ :=
    twoPointRelation_confluent_zero_zero w v u hwv hwu
  have hvu : v = u := by
    have hvx :=
      (relPow_zero_iff twoPointRelation v x).mp hxv
    have hux :=
      (relPow_zero_iff twoPointRelation u x).mp hxu
    exact hvx.trans hux.symm
  exact ⟨v,
    (twoPointRelation_even_relPow_iff k v v).mpr rfl,
    (twoPointRelation_even_relPow_iff l u v).mpr hvu.symm⟩

theorem twoPointRelation_confluent_odd_odd
    (k l : Nat) :
    confluent twoPointRelation (2 * k + 1) (2 * l + 1) := by
  intro w v u hwv hwu
  refine ⟨w, ?_, ?_⟩
  · exact (twoPointRelation_odd_relPow_iff k v w).mpr
      (Ne.symm hwv)
  · exact (twoPointRelation_odd_relPow_iff l u w).mpr
      (Ne.symm hwu)

theorem twoPointRelation_not_confluent_even_odd
    (k l : Nat) :
    ¬ confluent twoPointRelation (2 * k) (2 * l + 1) := by
  intro h
  have hwv : twoPointRelation (0 : Fin 2) 1 := by
    simp [twoPointRelation]
  obtain ⟨x, hxv, hxu⟩ := h 0 1 1 hwv hwv
  have heq :=
    (twoPointRelation_even_relPow_iff k 1 x).mp hxv
  have hne :=
    (twoPointRelation_odd_relPow_iff l 1 x).mp hxu
  exact hne heq

theorem twoPointRelation_not_confluent_odd_even
    (k l : Nat) :
    ¬ confluent twoPointRelation (2 * k + 1) (2 * l) := by
  intro h
  have hwv : twoPointRelation (0 : Fin 2) 1 := by
    simp [twoPointRelation]
  obtain ⟨x, hxv, hxu⟩ := h 0 1 1 hwv hwv
  have hne :=
    (twoPointRelation_odd_relPow_iff k 1 x).mp hxv
  have heq :=
    (twoPointRelation_even_relPow_iff l 1 x).mp hxu
  exact hne heq

theorem nat_even_or_odd_form
    (n : Nat) :
    (∃ k, n = 2 * k) ∨
    (∃ k, n = 2 * k + 1) := by
  induction n with
  | zero =>
    exact Or.inl ⟨0, by omega⟩
  | succ n ih =>
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · right
      exact ⟨k, by omega⟩
    · left
      exact ⟨k + 1, by omega⟩

theorem twoPointRelation_confluent_iff_parity
    (m n : Nat) :
    confluent twoPointRelation m n ↔ m % 2 = n % 2 := by
  constructor
  · intro h
    rcases nat_even_or_odd_form m with ⟨k, hk⟩ | ⟨k, hk⟩
    · rcases nat_even_or_odd_form n with ⟨l, hl⟩ | ⟨l, hl⟩
      · omega
      · have h' :
            confluent twoPointRelation (2 * k) (2 * l + 1) := by
          simpa [hk, hl] using h
        exact False.elim
          ((twoPointRelation_not_confluent_even_odd k l) h')
    · rcases nat_even_or_odd_form n with ⟨l, hl⟩ | ⟨l, hl⟩
      · have h' :
            confluent twoPointRelation (2 * k + 1) (2 * l) := by
          simpa [hk, hl] using h
        exact False.elim
          ((twoPointRelation_not_confluent_odd_even k l) h')
      · omega
  · intro hpar
    rcases nat_even_or_odd_form m with ⟨k, hk⟩ | ⟨k, hk⟩
    · rcases nat_even_or_odd_form n with ⟨l, hl⟩ | ⟨l, hl⟩
      · rw [hk, hl]
        exact twoPointRelation_confluent_even_even k l
      · have hf : False := by omega
        exact hf.elim
    · rcases nat_even_or_odd_form n with ⟨l, hl⟩ | ⟨l, hl⟩
      · have hf : False := by omega
        exact hf.elim
      · rw [hk, hl]
        exact twoPointRelation_confluent_odd_odd k l

theorem twoPointRelation_frameValid_iff_parity
    (m n : Nat) :
    frameValid twoPointRelation m n ↔ m % 2 = n % 2 := by
  rw [generalized_confluence_correspondence]
  exact twoPointRelation_confluent_iff_parity m n

def inequalityRelation {W : Type} : W → W → Prop :=
  fun x y => x ≠ y

def hasThirdPoint (W : Type) : Prop :=
  ∀ x y : W, ∃ z : W, z ≠ x ∧ z ≠ y

theorem inequalityRelation_relPow_ge_two
    {W : Type} (hthird : hasThirdPoint W) (n : Nat) :
    2 ≤ n → ∀ x y : W,
      relPow (inequalityRelation (W := W)) n x y := by
  change ∀ x y : W, ∃ z : W, z ≠ x ∧ z ≠ y at hthird
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn
      cases n with
      | zero =>
          omega
      | succ n =>
          cases n with
          | zero =>
              intro x y
              obtain ⟨z, hzx, hzy⟩ := hthird x y
              exact ⟨z, Ne.symm hzx, ⟨y, hzy, rfl⟩⟩
          | succ n =>
              intro x y
              obtain ⟨z, hzx, hzy⟩ := hthird x y
              exact ⟨z, Ne.symm hzx, ih (by omega) z y⟩



theorem inequalityRelation_confluent_ge_two
    {W : Type} (hthird : hasThirdPoint W)
    (m n : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    confluent (inequalityRelation (W := W)) m n := by
  intro w v u hwv hwu
  obtain ⟨x, hxv, hxu⟩ := hthird v u
  exact ⟨x,
    inequalityRelation_relPow_ge_two hthird m hm v x,
    inequalityRelation_relPow_ge_two hthird n hn u x⟩

theorem inequalityRelation_not_confluent_zero_zero
    {W : Type} (x y z : W)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    ¬ confluent (inequalityRelation (W := W)) 0 0 := by
  intro h
  obtain ⟨a, ha, hb⟩ := h x y z hxy hxz
  have hay : a = y := by
    simpa [relPow] using ha.symm
  have haz : a = z := by
    simpa [relPow] using hb.symm
  exact hyz (hay.symm.trans haz)

theorem inequalityRelation_not_confluent_zero_one
    {W : Type} (x y : W)
    (hxy : x ≠ y) :
    ¬ confluent (inequalityRelation (W := W)) 0 1 := by
  intro h
  obtain ⟨a, ha, hb⟩ := h x y y hxy hxy
  have hay : a = y := by
    simpa [relPow] using ha.symm
  subst a
  have hyy : inequalityRelation y y :=
    (relPow_one_iff inequalityRelation y y).mp hb
  exact hyy rfl

theorem inequalityRelation_not_confluent_one_zero
    {W : Type} (x y : W)
    (hxy : x ≠ y) :
    ¬ confluent (inequalityRelation (W := W)) 1 0 := by
  intro h
  obtain ⟨a, ha, hb⟩ := h x y y hxy hxy
  have hay : a = y := by
    simpa [relPow] using hb.symm
  subst a
  have hyy : inequalityRelation y y :=
    (relPow_one_iff inequalityRelation y y).mp ha
  exact hyy rfl

theorem inequalityRelation_not_confluent_below_two
    {W : Type} (w : W)
    (hthird : hasThirdPoint W)
    (m n : Nat)
    (hsmall : m + n < 2) :
    ¬ confluent (inequalityRelation (W := W)) m n := by
  obtain ⟨y, hyw, hyw'⟩ := hthird w w
  have hwy : w ≠ y := Ne.symm hyw
  obtain ⟨z, hzw, hzy⟩ := hthird w y
  have hwz : w ≠ z := Ne.symm hzw
  have hyz : y ≠ z := Ne.symm hzy
  cases m with
  | zero =>
    cases n with
    | zero =>
      exact inequalityRelation_not_confluent_zero_zero
        w y z hwy hwz hyz
    | succ n =>
      cases n with
      | zero =>
        exact inequalityRelation_not_confluent_zero_one
          w y hwy
      | succ n =>
        omega
  | succ m =>
    cases m with
    | zero =>
      cases n with
      | zero =>
        exact inequalityRelation_not_confluent_one_zero
          w y hwy
      | succ n =>
        omega
    | succ m =>
      omega



theorem inequalityRelation_common_target_ge_two
    {W : Type}
    (hthird : hasThirdPoint W)
    (m n : Nat)
    (hm : 2 ≤ m)
    (hn : 2 ≤ n)
    (v u : W) :
    ∃ x, relPow (inequalityRelation (W := W)) m v x ∧
         relPow (inequalityRelation (W := W)) n u x := by
  obtain ⟨x, hxv, hxu⟩ := hthird v u
  exact ⟨x,
    inequalityRelation_relPow_ge_two hthird m hm v x,
    inequalityRelation_relPow_ge_two hthird n hn u x⟩

theorem inequalityRelation_confluent_right_ge_two
    {W : Type} (hthird : hasThirdPoint W)
    (m n : Nat) (hn : 2 ≤ n) :
    confluent (inequalityRelation (W := W)) m n := by
  intro w v u hwv hwu
  cases m with
  | zero =>
      exact ⟨v,
        (relPow_zero_iff (inequalityRelation) v v).mpr rfl,
        inequalityRelation_relPow_ge_two hthird n hn u v⟩
  | succ m =>
      cases m with
      | zero =>
          exact ⟨w,
            (relPow_one_iff (inequalityRelation) v w).mpr (Ne.symm hwv),
            inequalityRelation_relPow_ge_two hthird n hn u w⟩
      | succ m =>
          exact ⟨w,
            inequalityRelation_relPow_ge_two hthird (m + 2) (by omega) v w,
            inequalityRelation_relPow_ge_two hthird n hn u w⟩

theorem inequalityRelation_confluent_left_ge_two
    {W : Type} (hthird : hasThirdPoint W)
    (m n : Nat) (hm : 2 ≤ m) :
    confluent (inequalityRelation (W := W)) m n := by
  intro w v u hwv hwu
  cases n with
  | zero =>
      exact ⟨u,
        inequalityRelation_relPow_ge_two hthird m hm v u,
        (relPow_zero_iff (inequalityRelation) u u).mpr rfl⟩
  | succ n =>
      cases n with
      | zero =>
          exact ⟨w,
            inequalityRelation_relPow_ge_two hthird m hm v w,
            (relPow_one_iff (inequalityRelation) u w).mpr (Ne.symm hwu)⟩
      | succ n =>
          exact ⟨w,
            inequalityRelation_relPow_ge_two hthird m hm v w,
            inequalityRelation_relPow_ge_two hthird (n + 2) (by omega) u w⟩



theorem inequalityRelation_confluent_one_one
    {W : Type} (hthird : hasThirdPoint W) :
    confluent (inequalityRelation (W := W)) 1 1 := by
  intro w v u hwv hwu
  obtain ⟨x, hxv, hxu⟩ := hthird v u
  exact ⟨x,
    (relPow_one_iff (inequalityRelation) v x).mpr (Ne.symm hxv),
    (relPow_one_iff (inequalityRelation) u x).mpr (Ne.symm hxu)⟩

theorem inequalityRelation_confluent_iff
    {W : Type} (w : W)
    (hthird : hasThirdPoint W)
    (m n : Nat) :
    confluent (inequalityRelation (W := W)) m n
      ↔ m + n ≥ 2 := by
  constructor
  · intro h
    by_cases hsmall : m + n < 2
    · exact False.elim
        ((inequalityRelation_not_confluent_below_two
          w hthird m n hsmall) h)
    · omega
  · intro hmn
    cases m with
    | zero =>
        have hn : 2 ≤ n := by omega
        exact inequalityRelation_confluent_right_ge_two
          hthird 0 n hn
    | succ m =>
        cases m with
        | zero =>
            cases n with
            | zero =>
                exact False.elim (by omega)
            | succ n =>
                cases n with
                | zero =>
                    exact inequalityRelation_confluent_one_one hthird
                | succ n =>
                    exact inequalityRelation_confluent_right_ge_two
                      hthird 1 (n + 2) (by omega)
        | succ m =>
            exact inequalityRelation_confluent_left_ge_two
              hthird (m + 2) n (by omega)

theorem inequalityRelation_frameValid_iff
    {W : Type} (w : W)
    (hthird : hasThirdPoint W)
    (m n : Nat) :
    frameValid (inequalityRelation (W := W)) m n
      ↔ m + n ≥ 2 := by
  rw [generalized_confluence_correspondence]
  exact inequalityRelation_confluent_iff w hthird m n

theorem inequalityRelation_confluent_iff_nonempty
    {W : Type} [Nonempty W]
    (hthird : hasThirdPoint W)
    (m n : Nat) :
    confluent (inequalityRelation (W := W)) m n
      ↔ m + n ≥ 2 := by
  obtain ⟨w⟩ := ‹Nonempty W›
  exact inequalityRelation_confluent_iff w hthird m n

theorem inequalityRelation_frameValid_iff_nonempty
    {W : Type} [Nonempty W]
    (hthird : hasThirdPoint W)
    (m n : Nat) :
    frameValid (inequalityRelation (W := W)) m n
      ↔ m + n ≥ 2 := by
  obtain ⟨w⟩ := ‹Nonempty W›
  exact inequalityRelation_frameValid_iff w hthird m n
theorem inequalityRelation_confluent_punit
    (m n : Nat) :
    confluent (inequalityRelation (W := PUnit)) m n := by
  intro w v u hwv hwu
  change w ≠ v at hwv
  exact False.elim (hwv (Subsingleton.elim w v))

theorem inequalityRelation_frameValid_punit
    (m n : Nat) :
    frameValid (inequalityRelation (W := PUnit)) m n := by
  rw [generalized_confluence_correspondence]
  exact inequalityRelation_confluent_punit m n

theorem inequalityRelation_relPow_iff
    {W : Type}
    (hthird : hasThirdPoint W)
    (n : Nat) (x y : W) :
    relPow (inequalityRelation (W := W)) n x y ↔
      (n = 0 ∧ x = y) ∨
      (n = 1 ∧ x ≠ y) ∨
      2 ≤ n := by
  cases n with
  | zero =>
      simp [relPow]
  | succ n =>
      cases n with
      | zero =>
          simp [relPow, inequalityRelation]
      | succ n =>
          constructor
          · intro _
            exact Or.inr (Or.inr (by omega))
          · intro _
            exact inequalityRelation_relPow_ge_two
              hthird (n + 2) (by omega) x y
theorem confluent_swap_exponents
    {W : Type} (R : W → W → Prop) (m n : Nat) :
    confluent R m n ↔ confluent R n m := by
  constructor
  · intro h w v u hwv hwu
    obtain ⟨x, hx1, hx2⟩ := h w u v hwu hwv
    exact ⟨x, hx2, hx1⟩
  · intro h w v u hwv hwu
    obtain ⟨x, hx1, hx2⟩ := h w u v hwu hwv
    exact ⟨x, hx2, hx1⟩

theorem frameValid_swap_exponents
    {W : Type} (R : W → W → Prop) (m n : Nat) :
    frameValid R m n ↔ frameValid R n m := by
  rw [generalized_confluence_correspondence R m n,
      generalized_confluence_correspondence R n m]
  exact confluent_swap_exponents R m n


theorem relPow_refl_of_reflexive
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (n : Nat) (x : W) :
    relPow R n x x := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      exact ⟨x, href x, ih⟩

theorem relPow_add_of_reflexive
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (m k : Nat) (x y : W)
    (hxy : relPow R m x y) :
    relPow R (m + k) x y := by
  induction k with
  | zero =>
      simpa using hxy
  | succ k ih =>
      change ∃ z, R x z ∧ relPow R (m + k) z y
      exact ⟨x, href x, ih⟩

theorem confluent_of_reflexive_symmetric_of_sum_ge_two
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (m n : Nat)
    (hmn : m + n ≥ 2) :
    confluent R m n := by
  intro w v u hwv hwu
  cases m with
  | zero =>
      cases n with
      | zero =>
          omega
      | succ n =>
          cases n with
          | zero =>
              omega
          | succ n =>
              have huv : relPow R 2 u v := by
                refine ⟨w, hsym w u hwu, ?_⟩
                exact (relPow_one_iff R w v).mpr hwv
              refine ⟨v, ?_, ?_⟩
              · exact (relPow_zero_iff R v v).mpr rfl
              · have hp :=
                  relPow_add_of_reflexive R href 2 n u v huv
                have hlen : 2 + n = n + 1 + 1 := by omega
                simpa [hlen] using hp
  | succ m =>
      cases n with
      | zero =>
          cases m with
          | zero =>
              omega
          | succ m =>
              have hvu : relPow R 2 v u := by
                refine ⟨w, hsym w v hwv, ?_⟩
                exact (relPow_one_iff R w u).mpr hwu
              refine ⟨u, ?_, ?_⟩
              · have hp :=
                  relPow_add_of_reflexive R href 2 m v u hvu
                have hlen : 2 + m = m + 1 + 1 := by omega
                simpa [hlen] using hp
              · exact (relPow_zero_iff R u u).mpr rfl
      | succ n =>
          refine ⟨w, ?_, ?_⟩
          · have hp :=
              relPow_add_of_reflexive R href 1 m v w
                ((relPow_one_iff R v w).mpr (hsym w v hwv))
            have hlen : 1 + m = m + 1 := by omega
            simpa [hlen] using hp
          · have hp :=
              relPow_add_of_reflexive R href 1 n u w
                ((relPow_one_iff R u w).mpr (hsym w u hwu))
            have hlen : 1 + n = n + 1 := by omega
            simpa [hlen] using hp

theorem frameValid_of_reflexive_symmetric_of_sum_ge_two
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (m n : Nat)
    (hmn : m + n ≥ 2) :
    frameValid R m n := by
  rw [generalized_confluence_correspondence R m n]
  exact confluent_of_reflexive_symmetric_of_sum_ge_two
    R href hsym m n hmn


theorem confluent_of_reflexive_symmetric_transitive_of_sum_ge_one
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat)
    (hmn : m + n ≥ 1) :
    confluent R m n := by
  intro w v u hwv hwu
  cases m with
  | zero =>
      cases n with
      | zero =>
          omega
      | succ n =>
          have huv : R u v :=
            htrans u w v (hsym w u hwu) hwv
          have hp :=
            relPow_add_of_reflexive R href 1 n u v
              ((relPow_one_iff R u v).mpr huv)
          have hlen : 1 + n = n + 1 := by omega
          exact ⟨v,
            (relPow_zero_iff R v v).mpr rfl,
            by simpa [hlen] using hp⟩
  | succ m =>
      cases n with
      | zero =>
          have hvu : R v u :=
            htrans v w u (hsym w v hwv) hwu
          have hp :=
            relPow_add_of_reflexive R href 1 m v u
              ((relPow_one_iff R v u).mpr hvu)
          have hlen : 1 + m = m + 1 := by omega
          exact ⟨u,
            by simpa [hlen] using hp,
            (relPow_zero_iff R u u).mpr rfl⟩
      | succ n =>
          have hvw : R v w := hsym w v hwv
          have huw : R u w := hsym w u hwu
          have hpv :=
            relPow_add_of_reflexive R href 1 m v w
              ((relPow_one_iff R v w).mpr hvw)
          have hpu :=
            relPow_add_of_reflexive R href 1 n u w
              ((relPow_one_iff R u w).mpr huw)
          have hlenv : 1 + m = m + 1 := by omega
          have hlenu : 1 + n = n + 1 := by omega
          exact ⟨w,
            by simpa [hlenv] using hpv,
            by simpa [hlenu] using hpu⟩
theorem frameValid_of_reflexive_symmetric_transitive_of_sum_ge_one
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat)
    (hmn : m + n ≥ 1) :
    frameValid R m n := by
  rw [generalized_confluence_correspondence R m n]
  exact confluent_of_reflexive_symmetric_transitive_of_sum_ge_one
    R href hsym htrans m n hmn

theorem confluent_zero_zero_iff_eq_relation
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x) :
    confluent R 0 0 ↔
      ∀ x y, R x y → x = y := by
  constructor
  · intro h x y hxy
    obtain ⟨z, hyz, hxz⟩ :=
      h x y x hxy (href x)
    have hyz' : y = z :=
      (relPow_zero_iff R y z).mp hyz
    have hxz' : x = z :=
      (relPow_zero_iff R x z).mp hxz
    exact hxz'.trans hyz'.symm
  · intro h w v u hwv hwu
    have hwv' : w = v := h w v hwv
    have hwu' : w = u := h w u hwu
    refine ⟨v, ?_, ?_⟩
    · exact (relPow_zero_iff R v v).mpr rfl
    · exact (relPow_zero_iff R u v).mpr
        (hwu'.symm.trans hwv')

theorem frameValid_zero_zero_iff_eq_relation
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x) :
    frameValid R 0 0 ↔
      ∀ x y, R x y → x = y := by
  rw [generalized_confluence_correspondence R 0 0]
  exact confluent_zero_zero_iff_eq_relation R href

theorem confluent_equivalence_relation_iff
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat) :
    confluent R m n ↔
      m + n ≥ 1 ∨ (∀ x y, R x y → x = y) := by
  constructor
  · intro h
    by_cases hpos : m + n ≥ 1
    · exact Or.inl hpos
    · right
      have hm : m = 0 := by omega
      have hn : n = 0 := by omega
      subst m
      subst n
      exact
        (confluent_zero_zero_iff_eq_relation R href).mp h
  · intro h
    rcases h with hpos | hsub
    · exact confluent_of_reflexive_symmetric_transitive_of_sum_ge_one
        R href hsym htrans m n hpos
    · intro w v u hwv hwu
      have hv : v = w := (hsub w v hwv).symm
      have hu : u = w := (hsub w u hwu).symm
      subst v
      subst u
      exact ⟨w,
        relPow_refl_of_reflexive R href m w,
        relPow_refl_of_reflexive R href n w⟩


theorem frameValid_equivalence_relation_iff
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat) :
    frameValid R m n ↔
      m + n ≥ 1 ∨ (∀ x y, R x y → x = y) := by
  rw [generalized_confluence_correspondence R m n]
  exact confluent_equivalence_relation_iff
    R href hsym htrans m n

theorem confluent_mono_exponents_of_reflexive
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (m n k l : Nat)
    (h : confluent R m n) :
    confluent R (m + k) (n + l) := by
  intro w v u hwv hwu
  obtain ⟨x, hvx, hux⟩ := h w v u hwv hwu
  exact ⟨x,
    relPow_add_of_reflexive R href m k v x hvx,
    relPow_add_of_reflexive R href n l u x hux⟩

theorem frameValid_mono_exponents_of_reflexive
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (m n k l : Nat)
    (h : frameValid R m n) :
    frameValid R (m + k) (n + l) := by
  have hc : confluent R m n :=
    (generalized_confluence_correspondence R m n).mp h
  exact (generalized_confluence_correspondence R (m + k) (n + l)).mpr
    (confluent_mono_exponents_of_reflexive
      R href m n k l hc)

theorem relPow_succ_of_loop_and_edge
    {W : Type} (R : W → W → Prop)
    {x y : W}
    (hloop : R x x)
    (hedge : R x y) :
    ∀ n : Nat, relPow R (n + 1) x y := by
  intro n
  induction n with
  | zero =>
      exact (relPow_one_iff R x y).mpr hedge
  | succ n ih =>
      exact ⟨x, hloop, ih⟩

theorem confluent_of_symmetric_transitive_of_sum_ge_one
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat)
    (hmn : m + n ≥ 1) :
    confluent R m n := by
  intro w v u hwv hwu

  have hvw : R v w := hsym w v hwv
  have huw : R u w := hsym w u hwu

  have hvv : R v v := htrans v w v hvw hwv
  have huu : R u u := htrans u w u huw hwu

  have hvu : R v u := htrans v w u hvw hwu
  have huv : R u v := htrans u w v huw hwv

  cases m with
  | zero =>
      cases n with
      | zero =>
          omega
      | succ n =>
          exact ⟨v,
            (relPow_zero_iff R v v).mpr rfl,
            relPow_succ_of_loop_and_edge R huu huv n⟩
  | succ m =>
      cases n with
      | zero =>
          exact ⟨u,
            relPow_succ_of_loop_and_edge R hvv hvu m,
            (relPow_zero_iff R u u).mpr rfl⟩
      | succ n =>
          exact ⟨w,
            relPow_succ_of_loop_and_edge R hvv hvw m,
            relPow_succ_of_loop_and_edge R huu huw n⟩

theorem frameValid_of_symmetric_transitive_of_sum_ge_one
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat)
    (hmn : m + n ≥ 1) :
    frameValid R m n := by
  rw [generalized_confluence_correspondence R m n]
  exact confluent_of_symmetric_transitive_of_sum_ge_one
    R hsym htrans m n hmn

theorem confluent_symmetric_transitive_iff
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat) :
    confluent R m n ↔
      m + n ≥ 1 ∨ (∀ x y, R x y → x = y) := by
  constructor
  · intro h
    by_cases hpos : m + n ≥ 1
    · exact Or.inl hpos
    · right
      have hm : m = 0 := by omega
      have hn : n = 0 := by omega
      subst m
      subst n
      intro x y hxy
      have hyx : R y x := hsym x y hxy
      have hxx : R x x := htrans x y x hxy hyx
      obtain ⟨z, hxz, hyz⟩ := h x x y hxx hxy
      have hxz' : x = z :=
        (relPow_zero_iff R x z).mp hxz
      have hyz' : y = z :=
        (relPow_zero_iff R y z).mp hyz
      exact hxz'.trans hyz'.symm
  · intro h
    rcases h with hpos | hdiag
    · exact confluent_of_symmetric_transitive_of_sum_ge_one
        R hsym htrans m n hpos
    · intro w v u hwv hwu
      have hv : v = w := (hdiag w v hwv).symm
      have hu : u = w := (hdiag w u hwu).symm
      have hww : R w w := by
        simpa [hv] using hwv
      have hloop : ∀ k : Nat, relPow R k w w := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => exact ⟨w, hww, ih⟩
      refine ⟨w, ?_, ?_⟩
      · simpa [hv] using hloop m
      · simpa [hu] using hloop n

theorem frameValid_symmetric_transitive_iff
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat) :
    frameValid R m n ↔
      m + n ≥ 1 ∨ (∀ x y, R x y → x = y) := by
  rw [generalized_confluence_correspondence R m n]
  exact confluent_symmetric_transitive_iff
    R hsym htrans m n
theorem confluent_symmetric_transitive_iff_positive
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (a b : W) (hab : R a b) (hne : a ≠ b)
    (m n : Nat) :
    confluent R m n ↔ m + n ≥ 1 := by
  rw [confluent_symmetric_transitive_iff R hsym htrans m n]
  constructor
  · intro h
    rcases h with hpos | hdiag
    · exact hpos
    · exact False.elim (hne (hdiag a b hab))
  · intro hpos
    exact Or.inl hpos

theorem frameValid_symmetric_transitive_iff_positive
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (a b : W) (hab : R a b) (hne : a ≠ b)
    (m n : Nat) :
    frameValid R m n ↔ m + n ≥ 1 := by
  rw [generalized_confluence_correspondence R m n]
  exact confluent_symmetric_transitive_iff_positive
    R hsym htrans a b hab hne m n

theorem relPow_pos_iff_of_symmetric_transitive
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (n : Nat) (x y : W) :
    relPow R (n + 1) x y ↔ R x y := by
  revert x y
  induction n with
  | zero =>
      intro x y
      exact relPow_one_iff R x y
  | succ n ih =>
      intro x y
      constructor
      · intro h
        obtain ⟨z, hxz, hzy⟩ := h
        exact htrans x z y hxz ((ih z y).mp hzy)
      · intro hxy
        have hxx : R x x :=
          htrans x y x hxy (hsym x y hxy)
        exact ⟨x, hxx, (ih x y).mpr hxy⟩

theorem relPow_zero_or_positive_iff
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (n : Nat) (x y : W) :
    relPow R n x y ↔
      (n = 0 ∧ x = y) ∨ (0 < n ∧ R x y) := by
  cases n with
  | zero =>
      simp [relPow]
  | succ n =>
      constructor
      · intro h
        right
        exact ⟨by omega,
          (relPow_pos_iff_of_symmetric_transitive
            R hsym htrans n x y).mp h⟩
      · intro h
        rcases h with hzero | hpos
        · omega
        · exact (relPow_pos_iff_of_symmetric_transitive
            R hsym htrans n x y).mpr hpos.2

theorem boxN_succ_iff_of_symmetric_transitive
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (n : Nat) (P : W → Prop) (w : W) :
    boxN R (n + 1) P w ↔ box R P w := by
  unfold boxN box
  constructor
  · intro h v hv
    exact h v
      ((relPow_pos_iff_of_symmetric_transitive
        R hsym htrans n w v).mpr hv)
  · intro h v hv
    exact h v
      ((relPow_pos_iff_of_symmetric_transitive
        R hsym htrans n w v).mp hv)

theorem diamondN_succ_iff_of_symmetric_transitive
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (n : Nat) (P : W → Prop) (w : W) :
    diamondN R (n + 1) P w ↔ diamond R P w := by
  unfold diamondN diamond
  constructor
  · rintro ⟨v, hv, hP⟩
    exact ⟨v,
      (relPow_pos_iff_of_symmetric_transitive
        R hsym htrans n w v).mp hv,
      hP⟩
  · rintro ⟨v, hv, hP⟩
    exact ⟨v,
      (relPow_pos_iff_of_symmetric_transitive
        R hsym htrans n w v).mpr hv,
      hP⟩

theorem frameValid_positive_exponents_iff
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat) :
    frameValid R (m + 1) (n + 1) ↔
      ∀ (P : W → Prop) (w : W),
        diamond R (box R P) w →
        box R (diamond R P) w := by
  unfold frameValid
  constructor
  · intro h P w hD
    change ∃ v, R w v ∧ box R P v at hD
    obtain ⟨v, hRv, hbox⟩ := hD
    have hboxN : boxN R (m + 1) P v :=
      (boxN_succ_iff_of_symmetric_transitive
        R hsym htrans m P v).mpr hbox
    have hD' : diamond R (boxN R (m + 1) P) w :=
      ⟨v, hRv, hboxN⟩
    have hout := h P w hD'
    change ∀ u, R w u → diamondN R (n + 1) P u at hout
    change ∀ u, R w u → diamond R P u
    intro u hwu
    exact (diamondN_succ_iff_of_symmetric_transitive
      R hsym htrans n P u).mp (hout u hwu)
  · intro h P w hD
    change ∃ v, R w v ∧ boxN R (m + 1) P v at hD
    obtain ⟨v, hRv, hboxN⟩ := hD
    have hbox : box R P v :=
      (boxN_succ_iff_of_symmetric_transitive
        R hsym htrans m P v).mp hboxN
    have hD' : diamond R (box R P) w :=
      ⟨v, hRv, hbox⟩
    have hout := h P w hD'
    change ∀ u, R w u → diamond R P u at hout
    change ∀ u, R w u → diamondN R (n + 1) P u
    intro u hwu
    exact (diamondN_succ_iff_of_symmetric_transitive
      R hsym htrans n P u).mpr (hout u hwu)

theorem ordinary_modal_condition_of_symmetric_transitive
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z) :
    ∀ (P : W → Prop) (w : W),
      diamond R (box R P) w →
      box R (diamond R P) w := by
  intro P w hD u hwu
  obtain ⟨v, hwv, hbox⟩ := hD
  have hvw : R v w := hsym w v hwv
  have hvu : R v u := htrans v w u hvw hwu
  have huv : R u v := hsym v u hvu
  have hvv : R v v := htrans v w v hvw hwv
  have hPv : P v := hbox v hvv
  exact ⟨v, huv, hPv⟩

theorem frameValid_symmetric_transitive_positive
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (m n : Nat) :
    frameValid R (m + 1) (n + 1) := by
  rw [frameValid_positive_exponents_iff R hsym htrans m n]
  exact ordinary_modal_condition_of_symmetric_transitive
    R hsym htrans

theorem twoPointRelation_not_confluent_two_one :
    ¬ confluent twoPointRelation 2 1 := by
  intro h
  have hp : 2 % 2 = 1 % 2 :=
    (twoPointRelation_confluent_iff_parity 2 1).mp h
  omega

theorem twoPointRelation_not_transitive :
    ¬ (∀ x y z : Fin 2,
        twoPointRelation x y →
        twoPointRelation y z →
        twoPointRelation x z) := by
  intro h
  have h01 : twoPointRelation (0 : Fin 2) 1 := by
    change (0 : Fin 2) ≠ 1
    decide
  have h10 : twoPointRelation (1 : Fin 2) 0 := by
    change (1 : Fin 2) ≠ 0
    decide
  have h00 : twoPointRelation (0 : Fin 2) 0 :=
    h 0 1 0 h01 h10
  exact h00 rfl

theorem twoPointRelation_not_frameValid_two_one :
    ¬ frameValid twoPointRelation 2 1 := by
  intro h
  have hc : confluent twoPointRelation 2 1 :=
    (generalized_confluence_correspondence
      twoPointRelation 2 1).mp h
  exact twoPointRelation_not_confluent_two_one hc

theorem confluent_one_zero_iff_transitive_of_symmetric
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x) :
    confluent R 1 0 ↔
      ∀ x y z, R x y → R y z → R x z := by
  constructor
  · intro h x y z hxy hyz
    have hyx : R y x := hsym x y hxy
    obtain ⟨t, hxt, hzt⟩ := h y x z hyx hyz
    have hzt' : z = t :=
      (relPow_zero_iff R z t).mp hzt
    subst t
    exact (relPow_one_iff R x z).mp hxt
  · intro htrans
    exact confluent_of_symmetric_transitive_of_sum_ge_one
      R hsym htrans 1 0 (by omega)

theorem frameValid_one_zero_iff_transitive_of_symmetric
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x) :
    frameValid R 1 0 ↔
      ∀ x y z, R x y → R y z → R x z := by
  rw [generalized_confluence_correspondence R 1 0]
  exact confluent_one_zero_iff_transitive_of_symmetric R hsym

theorem confluent_one_zero_iff_branch_property
    {W : Type} (R : W → W → Prop) :
    confluent R 1 0 ↔
      ∀ w v u, R w v → R w u → R v u := by
  constructor
  · intro h w v u hwv hwu
    obtain ⟨x, hvx, hux⟩ := h w v u hwv hwu
    have hvx' : R v x :=
      (relPow_one_iff R v x).mp hvx
    have hux' : x = u :=
    ((relPow_zero_iff R u x).mp hux).symm
    rw [hux'] at hvx'
    exact hvx'
  · intro h w v u hwv hwu
    refine ⟨u, ?_, ?_⟩
    · exact (relPow_one_iff R v u).mpr
        (h w v u hwv hwu)
    · exact (relPow_zero_iff R u u).mpr rfl

theorem frameValid_one_zero_iff_branch_property
    {W : Type} (R : W → W → Prop) :
    frameValid R 1 0 ↔
      ∀ w v u, R w v → R w u → R v u := by
  rw [generalized_confluence_correspondence R 1 0]
  exact confluent_one_zero_iff_branch_property R

theorem confluent_zero_one_iff_branch_property
    {W : Type} (R : W → W → Prop) :
    confluent R 0 1 ↔
      ∀ w v u, R w v → R w u → R u v := by
  constructor
  · intro h w v u hwv hwu
    obtain ⟨x, hvx, hux⟩ := h w v u hwv hwu
    have hvx' : v = x :=
      (relPow_zero_iff R v x).mp hvx
    subst x
    exact (relPow_one_iff R u v).mp hux
  · intro h w v u hwv hwu
    exact ⟨v,
      (relPow_zero_iff R v v).mpr rfl,
      (relPow_one_iff R u v).mpr (h w v u hwv hwu)⟩

theorem frameValid_zero_one_iff_branch_property
    {W : Type} (R : W → W → Prop) :
    frameValid R 0 1 ↔
      ∀ w v u, R w v → R w u → R u v := by
  rw [generalized_confluence_correspondence R 0 1]
  exact confluent_zero_one_iff_branch_property R

def oneStepDiamondProperty
    {W : Type} (R : W → W → Prop) : Prop :=
  ∀ w v u, R w v → R w u →
    ∃ x, R v x ∧ R u x

theorem oneStepDiamondProperty_iff_confluent_one_one
    {W : Type} (R : W → W → Prop) :
    oneStepDiamondProperty R ↔ confluent R 1 1 := by
  unfold oneStepDiamondProperty confluent
  constructor
  · intro h w v u hwv hwu
    obtain ⟨x, hvx, hux⟩ := h w v u hwv hwu
    exact ⟨x,
      (relPow_one_iff R v x).mpr hvx,
      (relPow_one_iff R u x).mpr hux⟩
  · intro h w v u hwv hwu
    obtain ⟨x, hvx, hux⟩ := h w v u hwv hwu
    exact ⟨x,
      (relPow_one_iff R v x).mp hvx,
      (relPow_one_iff R u x).mp hux⟩

theorem frameValid_one_one_iff_oneStepDiamondProperty
    {W : Type} (R : W → W → Prop) :
    frameValid R 1 1 ↔ oneStepDiamondProperty R := by
  rw [generalized_confluence_correspondence R 1 1]
  exact (oneStepDiamondProperty_iff_confluent_one_one R).symm

theorem oneStepDiamondProperty_of_symmetric
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x) :
    oneStepDiamondProperty R := by
  intro w v u hwv hwu
  exact ⟨w, hsym w v hwv, hsym w u hwu⟩

theorem frameValid_one_one_of_symmetric
    {W : Type} (R : W → W → Prop)
    (hsym : ∀ x y, R x y → R y x) :
    frameValid R 1 1 := by
  rw [frameValid_one_one_iff_oneStepDiamondProperty]
  exact oneStepDiamondProperty_of_symmetric R hsym

def twoPointOrderRelation
    (x y : Fin 2) : Prop :=
  x ≤ y

theorem twoPointOrderRelation_oneStepDiamond :
    oneStepDiamondProperty twoPointOrderRelation := by
  intro w v u _ _
  refine ⟨(1 : Fin 2), ?_, ?_⟩
  · exact Fin.le_last v
  · exact Fin.le_last u

theorem twoPointOrderRelation_not_symmetric :
    ¬ (∀ x y : Fin 2,
        twoPointOrderRelation x y →
        twoPointOrderRelation y x) := by
  intro h
  have h01 : twoPointOrderRelation (0 : Fin 2) 1 := by
    change (0 : Fin 2) ≤ 1
    decide
  have h10 : ¬ twoPointOrderRelation (1 : Fin 2) 0 := by
    change ¬ ((1 : Fin 2) ≤ 0)
    decide
  exact h10 (h 0 1 h01)



theorem twoPointOrderRelation_frameValid_one_one :
    frameValid twoPointOrderRelation 1 1 := by
  rw [frameValid_one_one_iff_oneStepDiamondProperty]
  exact twoPointOrderRelation_oneStepDiamond

theorem oneStepDiamondProperty_of_function_graph
    {W : Type} (f : W → W) :
    oneStepDiamondProperty (fun x y => y = f x) := by
  intro w v u hwv hwu
  change v = f w at hwv
  change u = f w at hwu
  subst v
  subst u
  exact ⟨f (f w), rfl, rfl⟩

theorem frameValid_one_one_of_function_graph
    {W : Type} (f : W → W) :
    frameValid (fun x y => y = f x) 1 1 := by
  rw [frameValid_one_one_iff_oneStepDiamondProperty]
  exact oneStepDiamondProperty_of_function_graph f

def functionIterate
    {W : Type} (f : W → W) : Nat → W → W
  | 0, x => x
  | n + 1, x => functionIterate f n (f x)

theorem functionIterate_surjective
    {W : Type} (f : W → W)
    (hf : Function.Surjective f)
    (n : Nat) :
    Function.Surjective (functionIterate f n) := by
  induction n with
  | zero =>
      intro y
      exact ⟨y, rfl⟩
  | succ n ih =>
      intro y
      obtain ⟨z, hz⟩ := ih y
      obtain ⟨x, hx⟩ := hf z
      refine ⟨x, ?_⟩
      simpa [functionIterate, hx] using hz



theorem relPow_functionGraph_iff
    {W : Type} (f : W → W)
    (n : Nat) (x y : W) :
    relPow (fun a b => b = f a) n x y
      ↔ y = functionIterate f n x := by
  induction n generalizing x y with
  | zero =>
      constructor
      · intro h
        exact h.symm
      · intro h
        exact h.symm
  | succ n ih =>
      constructor
      · rintro ⟨z, hz, hzy⟩
        subst z
        exact (ih (f x) y).mp hzy
      · intro h
        refine ⟨f x, rfl, ?_⟩
        exact (ih (f x) y).mpr h

theorem confluent_functionGraph_iff
    {W : Type} (f : W → W)
    (m n : Nat) :
    confluent (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (m + 1) w =
           functionIterate f (n + 1) w := by
  constructor
  · intro hc w
    obtain ⟨x, hx1, hx2⟩ :=
      hc w (f w) (f w) rfl rfl
    have h1 :=
      (relPow_functionGraph_iff f m (f w) x).mp hx1
    have h2 :=
      (relPow_functionGraph_iff f n (f w) x).mp hx2
    calc
      functionIterate f (m + 1) w = x := by
        simpa [functionIterate] using h1.symm
      _ = functionIterate f (n + 1) w := by
        simpa [functionIterate] using h2
  · intro h w v u hwv hwu
    change v = f w at hwv
    change u = f w at hwu
    subst v
    subst u
    refine ⟨functionIterate f (m + 1) w, ?_, ?_⟩
    · exact (relPow_functionGraph_iff f m (f w)
        (functionIterate f (m + 1) w)).mpr
          (by simp [functionIterate])
    · exact (relPow_functionGraph_iff f n (f w)
        (functionIterate f (m + 1) w)).mpr
          (by simpa [functionIterate] using h w)

theorem frameValid_functionGraph_iff
    {W : Type} (f : W → W)
    (m n : Nat) :
    frameValid (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (m + 1) w =
           functionIterate f (n + 1) w := by
  rw [generalized_confluence_correspondence]
  exact confluent_functionGraph_iff f m n

theorem confluent_functionGraph_zero_one_iff_idempotent
    {W : Type} (f : W → W) :
    confluent (fun x y => y = f x) 0 1 ↔
      ∀ w, f (f w) = f w := by
  rw [confluent_functionGraph_iff]
  constructor
  · intro h w
    have hw := h w
    change f w = f (f w) at hw
    exact hw.symm
  · intro h w
    change f w = f (f w)
    exact (h w).symm

theorem frameValid_functionGraph_zero_one_iff_idempotent
    {W : Type} (f : W → W) :
    frameValid (fun x y => y = f x) 0 1 ↔
      ∀ w, f (f w) = f w := by
  rw [frameValid_functionGraph_iff]
  constructor
  · intro h w
    have hw := h w
    simpa [functionIterate] using hw.symm
  · intro h w
    have hw := h w
    simpa [functionIterate] using hw.symm

theorem confluent_functionGraph_adjacent_iff
    {W : Type} (f : W → W) (m : Nat) :
    confluent (fun x y => y = f x) m (m + 1) ↔
      ∀ w, functionIterate f (m + 1) w =
           functionIterate f (m + 1 + 1) w := by
  exact confluent_functionGraph_iff f m (m + 1)

theorem functionIterate_succ_eq
    {W : Type} (f : W → W)
    (n : Nat) (w : W) :
    functionIterate f (n + 1) w =
      f (functionIterate f n w) := by
  induction n generalizing w with
  | zero =>
      rfl
  | succ n ih =>
      calc
        functionIterate f (Nat.succ (Nat.succ n)) w =
            functionIterate f (Nat.succ n) (f w) := rfl
        _ = f (functionIterate f n (f w)) := ih (f w)
        _ = f (functionIterate f (Nat.succ n) w) := rfl


theorem functionIterate_stable_of_adjacent
    {W : Type} (f : W → W)
    (m : Nat) (w : W)
    (h : functionIterate f (m + 1) w =
         functionIterate f (m + 2) w) :
    ∀ k : Nat,
      functionIterate f (m + 1 + k) w =
      functionIterate f (m + 1) w := by
  have hfix :
      f (functionIterate f (m + 1) w) =
      functionIterate f (m + 1) w := by
    rw [← functionIterate_succ_eq f (m + 1) w]
    exact h.symm
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hidx :
          m + 1 + Nat.succ k = (m + 1 + k) + 1 := by
        omega
      calc
        functionIterate f (m + 1 + Nat.succ k) w =
            functionIterate f ((m + 1 + k) + 1) w := by
              rw [hidx]
        _ = f (functionIterate f (m + 1 + k) w) :=
              functionIterate_succ_eq f (m + 1 + k) w
        _ = f (functionIterate f (m + 1) w) := by
              rw [ih]
        _ = functionIterate f (m + 1) w := hfix

theorem confluent_functionGraph_adjacent_stabilizes_all_later
    {W : Type} (f : W → W) (m : Nat)
    (h : confluent (fun x y => y = f x) m (m + 1)) :
    ∀ k : Nat,
      confluent (fun x y => y = f x) m (m + 1 + k) := by
  intro k
  apply (confluent_functionGraph_iff f m (m + 1 + k)).2
  intro w
  have hadj :
      functionIterate f (m + 1) w =
      functionIterate f (m + 1 + 1) w :=
    (confluent_functionGraph_adjacent_iff f m).mp h w
  have hstable :=
    functionIterate_stable_of_adjacent f m w hadj (k + 1)
  exact hstable.symm

theorem confluent_functionGraph_stable_from_threshold
    {W : Type} (f : W → W) (m : Nat)
    (h : confluent (fun x y => y = f x) m (m + 1)) :
    ∀ p q, m ≤ p → m ≤ q →
      confluent (fun x y => y = f x) p q := by
  intro p q hmp hmq
  apply (confluent_functionGraph_iff f p q).2
  intro w
  have hadj :=
    (confluent_functionGraph_adjacent_iff f m).mp h w
  have hpidx : p + 1 = m + 1 + (p - m) := by omega
  have hqidx : q + 1 = m + 1 + (q - m) := by omega
  rw [hpidx, hqidx]
  have hpStable :=
    functionIterate_stable_of_adjacent
      f m w hadj (p - m)
  have hqStable :=
    functionIterate_stable_of_adjacent
      f m w hadj (q - m)
  exact hpStable.trans hqStable.symm

theorem frameValid_functionGraph_stable_from_threshold
    {W : Type} (f : W → W) (m : Nat)
    (h : frameValid (fun x y => y = f x) m (m + 1)) :
    ∀ p q, m ≤ p → m ≤ q →
      frameValid (fun x y => y = f x) p q := by
  intro p q hmp hmq
  have hc :
      confluent (fun x y => y = f x) m (m + 1) :=
    (generalized_confluence_correspondence
      (fun x y => y = f x) m (m + 1)).mp h
  exact (generalized_confluence_correspondence
    (fun x y => y = f x) p q).mpr
      (confluent_functionGraph_stable_from_threshold
        f m hc p q hmp hmq)

theorem functionIterate_injective
    {W : Type} (f : W → W)
    (hf : Function.Injective f) :
    ∀ n : Nat, Function.Injective (functionIterate f n) := by
  intro n
  induction n with
  | zero =>
      intro x y h
      exact h
  | succ n ih =>
      intro x y h
      apply hf
      apply ih
      change functionIterate f n (f x) =
        functionIterate f n (f y) at h
      exact h

theorem function_eq_self_of_adjacent_iterates_of_injective
    {W : Type} (f : W → W)
    (hf : Function.Injective f)
    (m : Nat)
    (h : ∀ w,
      functionIterate f (m + 1) w =
      functionIterate f (m + 2) w) :
    ∀ w, f w = w := by
  intro w
  have hiter := h w
  have hcomp :
      functionIterate f (m + 1) w =
      functionIterate f (m + 1) (f w) := by
    simpa [functionIterate] using hiter
  have hinj :
      Function.Injective (functionIterate f (m + 1)) :=
    functionIterate_injective f hf (m + 1)
  have heq : w = f w := hinj hcomp
  exact heq.symm

theorem confluent_functionGraph_adjacent_iff_id_of_injective
    {W : Type} (f : W → W)
    (hf : Function.Injective f)
    (m : Nat) :
    confluent (fun x y => y = f x) m (m + 1) ↔
      ∀ w, f w = w := by
  rw [confluent_functionGraph_adjacent_iff]
  constructor
  · intro h
    exact function_eq_self_of_adjacent_iterates_of_injective
      f hf m h
  · intro h w
    have hiter : ∀ n, functionIterate f n w = w := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          simp [functionIterate, h w, ih]
    exact (hiter (m + 1)).trans (hiter (m + 2)).symm

theorem frameValid_functionGraph_adjacent_iff_id_of_injective
    {W : Type} (f : W → W)
    (hf : Function.Injective f)
    (m : Nat) :
    frameValid (fun x y => y = f x) m (m + 1) ↔
      ∀ w, f w = w := by
  rw [generalized_confluence_correspondence]
  exact confluent_functionGraph_adjacent_iff_id_of_injective
    f hf m

theorem functionIterate_add
    {W : Type} (f : W → W)
    (m n : Nat) (x : W) :
    functionIterate f (m + n) x =
      functionIterate f m (functionIterate f n x) := by
  induction n generalizing x with
  | zero =>
      simp [functionIterate]
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [functionIterate]
      exact ih (f x)

theorem functionIterate_eq_of_surjective
    {W : Type} (f : W → W)
    (hf : Function.Surjective f)
    (m n : Nat)
    (h : ∀ w, functionIterate f (m + 1) w =
              functionIterate f (n + 1) w) :
    ∀ w, functionIterate f m w =
         functionIterate f n w := by
  intro w
  obtain ⟨x, hx⟩ := hf w
  have h' := h x
  simpa [functionIterate, hx] using h'

theorem functionIterate_eq_iff_iterate_sub_eq_surjective
    {W : Type} (f : W → W)
    (hf : Function.Surjective f)
    (m n : Nat) (hmn : m ≤ n) :
    (∀ w, functionIterate f m w =
          functionIterate f n w) ↔
    (∀ w, functionIterate f (n - m) w = w) := by
  constructor
  · intro heq w
    obtain ⟨x, hx⟩ :=
      functionIterate_surjective f hf m w
    have hidx : n = m + (n - m) := by omega
    have heq' := heq x
    rw [hidx, functionIterate_add] at heq'
    calc
      functionIterate f (n - m) w =
          functionIterate f (n - m)
            (functionIterate f m x) := by rw [hx]
      _ = functionIterate f m
            (functionIterate f (n - m) x) := by
        calc
          _ = functionIterate f ((n - m) + m) x :=
            (functionIterate_add f (n - m) m x).symm
          _ = functionIterate f (m + (n - m)) x := by
            rw [Nat.add_comm]
          _ = _ := functionIterate_add f m (n - m) x
      _ = functionIterate f m x := heq'.symm
      _ = w := hx
  · intro hfix w
    have hidx : n = m + (n - m) := by omega
    calc
      functionIterate f m w =
          functionIterate f m
            (functionIterate f (n - m) w) := by
        rw [hfix w]
      _ = functionIterate f (m + (n - m)) w :=
        (functionIterate_add f m (n - m) w).symm
      _ = functionIterate f n w := by rw [← hidx]

theorem functionIterate_eq_iff_abs_sub_eq
    {W : Type} (f : W → W)
    (hf : Function.Surjective f)
    (m n : Nat) :
    (∀ w, functionIterate f m w =
          functionIterate f n w) ↔
    (∀ w, functionIterate f (Nat.max m n - Nat.min m n) w = w) := by
  by_cases hmn : m ≤ n
  · have h :=
      functionIterate_eq_iff_iterate_sub_eq_surjective
        f hf m n hmn
    simpa [Nat.max_eq_right hmn, Nat.min_eq_left hmn] using h
  · have hnm : n ≤ m := by omega
    have h :=
      functionIterate_eq_iff_iterate_sub_eq_surjective
        f hf n m hnm
    constructor
    · intro heq
      have heq' : ∀ w,
          functionIterate f n w = functionIterate f m w := by
        intro w
        exact (heq w).symm
      have hfix := h.mp heq'
      simpa [Nat.max_eq_left hnm, Nat.min_eq_right hnm] using hfix
    · intro hfix w
      have hfix' : ∀ w,
          functionIterate f (m - n) w = w := by
        simpa [Nat.max_eq_left hnm, Nat.min_eq_right hnm] using hfix
      exact (h.mpr hfix' w).symm

theorem confluent_functionGraph_iff_abs_sub_eq
    {W : Type} (f : W → W)
    (hf : Function.Surjective f)
    (m n : Nat) :
    confluent (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f
        (Nat.max m n - Nat.min m n) w = w := by
  rw [confluent_functionGraph_iff]
  have hshift :
      (∀ w, functionIterate f (m + 1) w =
            functionIterate f (n + 1) w) ↔
      (∀ w, functionIterate f m w =
            functionIterate f n w) := by
    constructor
    · intro h
      exact functionIterate_eq_of_surjective f hf m n h
    · intro h w
      simpa [functionIterate] using h (f w)
  exact hshift.trans
    (functionIterate_eq_iff_abs_sub_eq f hf m n)

theorem functionGraph_reflexive_iff_eq_id
    {W : Type} (f : W → W) :
    (∀ x, (fun a b => b = f a) x x) ↔
      f = id := by
  constructor
  · intro h
    funext x
    exact (h x).symm
  · intro h x
    have hx := congrFun h x
    simpa using hx.symm

/-
theorem confluent_functionGraph_iff_iterate_sub_eq_self
    {W : Type} (f : W → W)
    (hf : Function.Injective f)
    (m n : Nat) (hmn : m ≤ n) :
    confluent (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (n - m) w = w := by
  rw [confluent_functionGraph_iff]
  have hidx : (n + 1) - (m + 1) = n - m := by omega
  simpa only [hidx] using
    (functionIterate_eq_iff_iterate_sub_eq_self
      f hf (m + 1) (n + 1) (by omega))
-/
/-
theorem frameValid_functionGraph_iff_iterate_sub_eq_self
    {W : Type} (f : W → W)
    (hf : Function.Injective f)
    (m n : Nat) (hmn : m ≤ n) :
    frameValid (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (n - m) w = w := by
  rw [generalized_confluence_correspondence]
  exact confluent_functionGraph_iff_iterate_sub_eq_self
    f hf m n hmn
-/
theorem confluent_functionGraph_iff_eventual_period
    {W : Type} (f : W → W)
    (m n : Nat) (hmn : m ≤ n) :
    confluent (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (m + 1) w =
        functionIterate f (m + 1)
          (functionIterate f (n - m) w) := by
  rw [confluent_functionGraph_iff]
  have hidx : (m + 1) + (n - m) = n + 1 := by omega
  constructor
  · intro h w
    calc
      functionIterate f (m + 1) w =
          functionIterate f (n + 1) w := h w
      _ = functionIterate f ((m + 1) + (n - m)) w := by
        rw [hidx]
      _ = functionIterate f (m + 1)
          (functionIterate f (n - m) w) :=
        functionIterate_add f (m + 1) (n - m) w
  · intro h w
    calc
      functionIterate f (m + 1) w =
          functionIterate f (m + 1)
            (functionIterate f (n - m) w) := h w
      _ = functionIterate f ((m + 1) + (n - m)) w :=
        (functionIterate_add f (m + 1) (n - m) w).symm
      _ = functionIterate f (n + 1) w := by
        rw [hidx]

theorem frameValid_functionGraph_iff_eventual_period
    {W : Type} (f : W → W)
    (m n : Nat) (hmn : m ≤ n) :
    frameValid (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (m + 1) w =
        functionIterate f (m + 1)
          (functionIterate f (n - m) w) := by
  rw [generalized_confluence_correspondence]
  exact confluent_functionGraph_iff_eventual_period
    f m n hmn

theorem confluent_functionGraph_iff_min_max
    {W : Type} (f : W → W)
    (m n : Nat) :
    confluent (fun x y => y = f x) m n ↔
      ∀ w,
        functionIterate f (min m n + 1) w =
        functionIterate f (min m n + 1)
          (functionIterate f (max m n - min m n) w) := by
  by_cases hmn : m ≤ n
  · have hchar :=
      confluent_functionGraph_iff_eventual_period
        f m n hmn
    have hmin : min m n = m := by omega
    have hmax : max m n = n := by omega
    simpa [hmin, hmax] using hchar
  · have hnm : n ≤ m := by omega
    have hchar :=
      (confluent_swap_exponents
        (fun x y => y = f x) m n).trans
        (confluent_functionGraph_iff_eventual_period
          f n m hnm)
    have hmin : min m n = n := by omega
    have hmax : max m n = m := by omega
    simpa [hmin, hmax] using hchar

theorem frameValid_functionGraph_iff_min_max
    {W : Type} (f : W → W)
    (m n : Nat) :
    frameValid (fun x y => y = f x) m n ↔
      ∀ w,
        functionIterate f (min m n + 1) w =
        functionIterate f (min m n + 1)
          (functionIterate f (max m n - min m n) w) := by
  rw [generalized_confluence_correspondence]
  exact confluent_functionGraph_iff_min_max f m n

theorem confluent_functionGraph_iff_periodic_of_injective
    {W : Type} (f : W → W)
    (hf : Function.Injective f)
    (m n : Nat) :
    confluent (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (max m n - min m n) w = w := by
  rw [confluent_functionGraph_iff_min_max]
  constructor
  · intro h w
    have hinj :
        Function.Injective (functionIterate f (min m n + 1)) :=
      functionIterate_injective f hf (min m n + 1)
    exact (hinj (h w)).symm
  · intro h w
    exact
      (congrArg (functionIterate f (min m n + 1)) (h w)).symm

theorem frameValid_functionGraph_iff_periodic_of_injective
    {W : Type} (f : W → W)
    (hf : Function.Injective f)
    (m n : Nat) :
    frameValid (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (max m n - min m n) w = w := by
  rw [generalized_confluence_correspondence
    (fun x y => y = f x) m n]
  exact confluent_functionGraph_iff_periodic_of_injective
    f hf m n

theorem confluent_functionGraph_of_idempotent
    {W : Type} (f : W → W)
    (hidem : ∀ w, f (f w) = f w)
    (m n : Nat) :
    confluent (fun x y => y = f x) m n := by
  have h01 : confluent (fun x y => y = f x) 0 1 :=
    (confluent_functionGraph_zero_one_iff_idempotent f).mpr hidem
  exact
    confluent_functionGraph_stable_from_threshold
      f 0 h01 m n (by omega) (by omega)

theorem frameValid_functionGraph_of_idempotent
    {W : Type} (f : W → W)
    (hidem : ∀ w, f (f w) = f w)
    (m n : Nat) :
    frameValid (fun x y => y = f x) m n := by
  rw [generalized_confluence_correspondence]
  exact confluent_functionGraph_of_idempotent f hidem m n

theorem confluent_functionGraph_all_iff_idempotent
    {W : Type} (f : W → W) :
    (∀ m n, confluent (fun x y => y = f x) m n) ↔
      ∀ w, f (f w) = f w := by
  constructor
  · intro h
    exact
      (confluent_functionGraph_zero_one_iff_idempotent f).mp
        (h 0 1)
  · intro hidem m n
    exact confluent_functionGraph_of_idempotent
      f hidem m n

theorem frameValid_functionGraph_all_iff_idempotent
    {W : Type} (f : W → W) :
    (∀ m n, frameValid (fun x y => y = f x) m n) ↔
      ∀ w, f (f w) = f w := by
  constructor
  · intro h
    have h01 : frameValid (fun x y => y = f x) 0 1 :=
      h 0 1
    have hc : confluent (fun x y => y = f x) 0 1 :=
      (generalized_confluence_correspondence
        (fun x y => y = f x) 0 1).mp h01
    exact
      (confluent_functionGraph_zero_one_iff_idempotent f).mp hc
  · intro hidem m n
    exact frameValid_functionGraph_of_idempotent
      f hidem m n

theorem functionGraph_symmetric_iff_involutive
    {W : Type} (f : W → W) :
    (∀ x y, (y = f x) → (x = f y)) ↔
      ∀ x, f (f x) = x := by
  constructor
  · intro h x
    exact (h x (f x) rfl).symm
  · intro h x y hxy
    subst y
    exact (h x).symm

theorem functionGraph_transitive_iff_idempotent
    {W : Type} (f : W → W) :
    (∀ x y z, (y = f x) → (z = f y) → (z = f x)) ↔
      ∀ x, f (f x) = f x := by
  constructor
  · intro h x
    exact h x (f x) (f (f x)) rfl rfl
  · intro hidem x y z hxy hyz
    subst y
    subst z
    exact hidem x

theorem functionGraph_symmetric_transitive_iff_identity
    {W : Type} (f : W → W) :
    ((∀ x y, y = f x → x = f y) ∧
     (∀ x y z, y = f x → z = f y → z = f x)) ↔
      ∀ x, f x = x := by
  constructor
  · rintro ⟨hs, ht⟩ x
    have hinv :=
      (functionGraph_symmetric_iff_involutive f).mp hs x
    have hidem :=
      (functionGraph_transitive_iff_idempotent f).mp ht x
    exact (hidem).symm.trans hinv
  · intro hid
    constructor
    · exact (functionGraph_symmetric_iff_involutive f).mpr
        (by
          intro x
          calc
            f (f x) = f x := hid (f x)
            _ = x := hid x)
    · exact (functionGraph_transitive_iff_idempotent f).mpr
        (by
          intro x
          exact hid (f x))

theorem confluent_functionGraph_zero_one_iff_identity_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y) :
    confluent (fun x y => y = f x) 0 1 ↔
      ∀ x, f x = x := by
  constructor
  · intro hc
    have hidem :=
      (confluent_functionGraph_zero_one_iff_idempotent f).mp hc
    have hinv :=
      (functionGraph_symmetric_iff_involutive f).mp hsym
    intro x
    calc
      f x = f (f x) := (hidem x).symm
      _ = x := hinv x
  · intro hid
    apply (confluent_functionGraph_zero_one_iff_idempotent f).mpr
    intro x
    rw [hid (f x)]

theorem frameValid_functionGraph_zero_one_iff_identity_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y) :
    frameValid (fun x y => y = f x) 0 1 ↔
      ∀ x, f x = x := by
  rw [generalized_confluence_correspondence
    (fun x y => y = f x) 0 1]
  exact confluent_functionGraph_zero_one_iff_identity_of_symmetric
    f hsym

theorem confluent_functionGraph_one_zero_iff_idempotent
    {W : Type} (f : W → W) :
    confluent (fun x y => y = f x) 1 0 ↔
      ∀ w, f (f w) = f w := by
  rw [confluent_swap_exponents]
  exact confluent_functionGraph_zero_one_iff_idempotent f

theorem frameValid_functionGraph_one_zero_iff_idempotent
    {W : Type} (f : W → W) :
    frameValid (fun x y => y = f x) 1 0 ↔
      ∀ w, f (f w) = f w := by
  rw [generalized_confluence_correspondence
    (fun x y => y = f x) 1 0]
  exact confluent_functionGraph_one_zero_iff_idempotent f

theorem frameValid_functionGraph_one_zero_iff_identity_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y) :
    frameValid (fun x y => y = f x) 1 0 ↔
      ∀ x, f x = x := by
  constructor
  · intro hv
    have hidem :=
      (frameValid_functionGraph_one_zero_iff_idempotent f).mp hv
    have hinv :=
      (functionGraph_symmetric_iff_involutive f).mp hsym
    intro x
    calc
      f x = f (f x) := (hidem x).symm
      _ = x := hinv x
  · intro hid
    exact
      (frameValid_functionGraph_one_zero_iff_idempotent f).mpr
        (by
          intro x
          exact hid (f x))

theorem functionGraph_injective_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y) :
    Function.Injective f := by
  have hinv :=
    (functionGraph_symmetric_iff_involutive f).mp hsym
  intro x y hxy
  have h := congrArg f hxy
  simpa only [hinv x, hinv y] using h

theorem confluent_functionGraph_iff_periodic_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y)
    (m n : Nat) :
    confluent (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (max m n - min m n) w = w := by
  exact confluent_functionGraph_iff_periodic_of_injective
    f (functionGraph_injective_of_symmetric f hsym) m n

theorem frameValid_functionGraph_iff_periodic_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y)
    (m n : Nat) :
    frameValid (fun x y => y = f x) m n ↔
      ∀ w, functionIterate f (max m n - min m n) w = w := by
  rw [generalized_confluence_correspondence
    (fun x y => y = f x) m n]
  exact confluent_functionGraph_iff_periodic_of_symmetric
    f hsym m n

theorem functionIterate_involution_even
    {W : Type} (f : W → W)
    (hinv : ∀ x, f (f x) = x) :
    ∀ n x, functionIterate f (2 * n) x = x := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      have htwo : functionIterate f 2 x = x := by
        simp [functionIterate, hinv]
      calc
        functionIterate f (2 * (n + 1)) x =
            functionIterate f (2 * n + 2) x := by
              congr 1
        _ = functionIterate f (2 * n)
              (functionIterate f 2 x) := by
              exact functionIterate_add f (2 * n) 2 x
        _ = functionIterate f (2 * n) x := by
              rw [htwo]
        _ = x := ih x

theorem functionIterate_involution_odd
    {W : Type} (f : W → W)
    (hinv : ∀ x, f (f x) = x) :
    ∀ n x, functionIterate f (2 * n + 1) x = f x := by
  intro n x
  calc
    functionIterate f (2 * n + 1) x =
        functionIterate f (2 * n)
          (functionIterate f 1 x) :=
      functionIterate_add f (2 * n) 1 x
    _ = functionIterate f (2 * n) (f x) := by
      rfl
    _ = f x :=
      functionIterate_involution_even f hinv n (f x)

theorem confluent_functionGraph_iff_parity_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y)
    (m n : Nat) :
    confluent (fun x y => y = f x) m n ↔
      (max m n - min m n) % 2 = 0 ∨
      (∀ w, f w = w) := by
  rw [confluent_functionGraph_iff_periodic_of_symmetric
    f hsym m n]
  let d := max m n - min m n
  change (∀ w, functionIterate f d w = w) ↔
    (max m n - min m n) % 2 = 0 ∨
      (∀ w, f w = w)
  have hinv :=
    (functionGraph_symmetric_iff_involutive f).mp hsym
  constructor
  · intro h
    by_cases heven : d % 2 = 0
    · left
      simpa [d] using heven
    · right
      have hodd : d % 2 = 1 := by omega
      have hd : d = 2 * (d / 2) + 1 := by omega
      intro w
      have hw := h w
      rw [hd, functionIterate_involution_odd f hinv (d / 2) w] at hw
      exact hw
  · intro h
    rcases h with heven | hid
    · have hdEven : d % 2 = 0 := by
        simpa [d] using heven
      have hd : d = 2 * (d / 2) := by omega
      intro w
      rw [hd]
      exact functionIterate_involution_even f hinv (d / 2) w
    · intro w
      have hiter : ∀ k, functionIterate f k w = w := by
        intro k
        induction k with
        | zero =>
            rfl
        | succ k ih =>
            change functionIterate f k (f w) = w
            rw [hid w]
            exact ih
      exact hiter d

theorem frameValid_functionGraph_iff_parity_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y)
    (m n : Nat) :
    frameValid (fun x y => y = f x) m n ↔
      (max m n - min m n) % 2 = 0 ∨
      (∀ w, f w = w) := by
  rw [generalized_confluence_correspondence
    (fun x y => y = f x) m n]
  exact confluent_functionGraph_iff_parity_of_symmetric
    f hsym m n

theorem nat_abs_diff_even_iff_sum_even
    (m n : Nat) :
    (max m n - min m n) % 2 = 0 ↔
      (m + n) % 2 = 0 := by
  by_cases hmn : m ≤ n
  · have hmin : min m n = m := by omega
    have hmax : max m n = n := by omega
    omega
  · have hnm : n ≤ m := by omega
    have hmin : min m n = n := by omega
    have hmax : max m n = m := by omega
    omega

theorem confluent_functionGraph_iff_sum_even_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y)
    (m n : Nat) :
    confluent (fun x y => y = f x) m n ↔
      (m + n) % 2 = 0 ∨ (∀ w, f w = w) := by
  rw [confluent_functionGraph_iff_parity_of_symmetric
    f hsym m n]
  rw [nat_abs_diff_even_iff_sum_even m n]

theorem frameValid_functionGraph_iff_sum_even_of_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y)
    (m n : Nat) :
    frameValid (fun x y => y = f x) m n ↔
      (m + n) % 2 = 0 ∨ (∀ w, f w = w) := by
  rw [generalized_confluence_correspondence
    (fun x y => y = f x) m n]
  exact confluent_functionGraph_iff_sum_even_of_symmetric
    f hsym m n

theorem frameValid_functionGraph_iff_sum_even_of_nonidentity_symmetric
    {W : Type} (f : W → W)
    (hsym : ∀ x y, y = f x → x = f y)
    (hnotid : ¬ (∀ w, f w = w))
    (m n : Nat) :
    frameValid (fun x y => y = f x) m n ↔
      (m + n) % 2 = 0 := by
  rw [frameValid_functionGraph_iff_sum_even_of_symmetric
    f hsym m n]
  constructor
  · intro h
    rcases h with heven | hid
    · exact heven
    · exact False.elim (hnotid hid)
  · intro heven
    exact Or.inl heven

def boolSwap (x : Bool) : Bool := !x

theorem boolSwap_symmetric :
    ∀ x y : Bool,
      y = boolSwap x → x = boolSwap y := by
  intro x y h
  subst y
  cases x <;> rfl

theorem boolSwap_not_identity :
    ¬ (∀ x : Bool, boolSwap x = x) := by
  intro h
  have htrue := h true
  simp [boolSwap] at htrue

theorem frameValid_boolSwap_iff_sum_even
    (m n : Nat) :
    frameValid (fun x y : Bool => y = boolSwap x) m n ↔
      (m + n) % 2 = 0 := by
  exact frameValid_functionGraph_iff_sum_even_of_nonidentity_symmetric
    boolSwap boolSwap_symmetric boolSwap_not_identity m n

theorem not_frameValid_boolSwap_of_sum_odd
    (m n : Nat)
    (hodd : (m + n) % 2 = 1) :
    ¬ frameValid (fun x y : Bool => y = boolSwap x) m n := by
  intro hv
  have heven :=
    (frameValid_boolSwap_iff_sum_even m n).mp hv
  omega

theorem functionIterate_mul_eq_self
    {W : Type} (f : W → W)
    (k : Nat) (w : W)
    (hperiod : functionIterate f k w = w) :
    ∀ q : Nat, functionIterate f (k * q) w = w := by
  intro q
  induction q with
  | zero =>
      simp [functionIterate]
  | succ q ih =>
      rw [Nat.mul_succ]
      calc
        functionIterate f (k * q + k) w =
            functionIterate f (k * q)
              (functionIterate f k w) :=
          functionIterate_add f (k * q) k w
        _ = functionIterate f (k * q) w := by
          rw [hperiod]
        _ = w := ih

theorem functionIterate_eq_self_of_period_dvd
    {W : Type} (f : W → W)
    (k d : Nat) (w : W)
    (hperiod : functionIterate f k w = w)
    (hdiv : ∃ q : Nat, d = k * q) :
    functionIterate f d w = w := by
  obtain ⟨q, hq⟩ := hdiv
  rw [hq]
  exact functionIterate_mul_eq_self f k w hperiod q

theorem confluent_functionGraph_of_uniform_period_dvd
    {W : Type} (f : W → W)
    (k m n : Nat)
    (hperiod : ∀ w, functionIterate f k w = w)
    (hdiv : ∃ q : Nat,
      max m n - min m n = k * q) :
    confluent (fun x y => y = f x) m n := by
  apply (confluent_functionGraph_iff_min_max f m n).2
  intro w
  have hfix :=
    functionIterate_eq_self_of_period_dvd
      f k (max m n - min m n) w (hperiod w) hdiv
  exact
    (congrArg
      (functionIterate f (min m n + 1)) hfix).symm

theorem frameValid_functionGraph_of_uniform_period_dvd
    {W : Type} (f : W → W)
    (k m n : Nat)
    (hperiod : ∀ w, functionIterate f k w = w)
    (hdiv : ∃ q : Nat,
      max m n - min m n = k * q) :
    frameValid (fun x y => y = f x) m n := by
  rw [generalized_confluence_correspondence
    (fun x y => y = f x) m n]
  exact confluent_functionGraph_of_uniform_period_dvd
    f k m n hperiod hdiv

def IsLeastUniformPeriod
    {W : Type} (f : W → W) (k : Nat) : Prop :=
  0 < k ∧
  (∀ w, functionIterate f k w = w) ∧
  (∀ j : Nat, 0 < j → j < k →
    ¬ (∀ w, functionIterate f j w = w))

theorem exists_mul_eq_of_isLeastUniformPeriod
    {W : Type} (f : W → W)
    (k d : Nat)
    (hleast : IsLeastUniformPeriod f k)
    (hperiod : ∀ w, functionIterate f d w = w) :
    ∃ q : Nat, d = k * q := by
  rcases hleast with ⟨hkpos, hkperiod, hminimal⟩
  have hdecomp : d % k + k * (d / k) = d :=
    Nat.mod_add_div d k
  have hrem : ∀ w, functionIterate f (d % k) w = w := by
    intro w
    have hdw := hperiod w
    rw [← hdecomp, functionIterate_add] at hdw
    have hmult :=
      functionIterate_mul_eq_self f k w (hkperiod w) (d / k)
    rw [hmult] at hdw
    exact hdw
  by_cases hr : d % k = 0
  · have hd : d = k * (d / k) := by
      calc
        d = d % k + k * (d / k) := hdecomp.symm
        _ = k * (d / k) := by rw [hr]; simp
    exact ⟨d / k, hd⟩
  · have hrpos : 0 < d % k := Nat.pos_of_ne_zero hr
    have hrlt : d % k < k := Nat.mod_lt d hkpos
    exact False.elim (hminimal (d % k) hrpos hrlt hrem)

theorem function_injective_of_uniform_period
    {W : Type} (f : W → W)
    (k : Nat)
    (hkpos : 0 < k)
    (hperiod : ∀ w, functionIterate f k w = w) :
    Function.Injective f := by
  intro x y hxy
  have hiter :
      functionIterate f (k - 1) (f x) =
      functionIterate f (k - 1) (f y) :=
    congrArg (functionIterate f (k - 1)) hxy
  have hx :
      functionIterate f (k - 1) (f x) = x := by
    calc
      functionIterate f (k - 1) (f x) =
          functionIterate f (k - 1)
            (functionIterate f 1 x) := by rfl
      _ = functionIterate f ((k - 1) + 1) x :=
          (functionIterate_add f (k - 1) 1 x).symm
      _ = functionIterate f k x := by
          rw [Nat.sub_add_cancel hkpos]
      _ = x := hperiod x
  have hy :
      functionIterate f (k - 1) (f y) = y := by
    calc
      functionIterate f (k - 1) (f y) =
          functionIterate f (k - 1)
            (functionIterate f 1 y) := by rfl
      _ = functionIterate f ((k - 1) + 1) y :=
          (functionIterate_add f (k - 1) 1 y).symm
      _ = functionIterate f k y := by
          rw [Nat.sub_add_cancel hkpos]
      _ = y := hperiod y
  exact hx.symm.trans (hiter.trans hy)

theorem confluent_functionGraph_iff_dvd_of_least_period
    {W : Type} (f : W → W)
    (k m n : Nat)
    (hleast : IsLeastUniformPeriod f k) :
    confluent (fun x y => y = f x) m n ↔
      ∃ q : Nat, max m n - min m n = k * q := by
  rcases hleast with ⟨hkpos, hkperiod, hminimal⟩
  constructor
  · intro hc
    apply exists_mul_eq_of_isLeastUniformPeriod
      f k (max m n - min m n)
      ⟨hkpos, hkperiod, hminimal⟩
    intro w
    have hdiamond :=
      (confluent_functionGraph_iff_min_max f m n).mp hc w
    have hinj :=
      functionIterate_injective f
        (function_injective_of_uniform_period
          f k hkpos hkperiod)
        (min m n + 1)
    exact (hinj hdiamond).symm
  · intro hdiv
    exact confluent_functionGraph_of_uniform_period_dvd
      f k m n hkperiod hdiv

theorem frameValid_functionGraph_iff_dvd_of_least_period
    {W : Type} (f : W → W)
    (k m n : Nat)
    (hleast : IsLeastUniformPeriod f k) :
    frameValid (fun x y => y = f x) m n ↔
      ∃ q : Nat, max m n - min m n = k * q := by
  rw [generalized_confluence_correspondence
    (fun x y => y = f x) m n]
  exact confluent_functionGraph_iff_dvd_of_least_period
    f k m n hleast

theorem isLeastUniformPeriod_unique
    {W : Type} (f : W → W)
    (k l : Nat)
    (hk : IsLeastUniformPeriod f k)
    (hl : IsLeastUniformPeriod f l) :
    k = l := by
  rcases hk with ⟨hkpos, hkperiod, hkminimal⟩
  rcases hl with ⟨hlpos, hlperiod, hlminimal⟩
  have hkl :=
    exists_mul_eq_of_isLeastUniformPeriod
      f k l ⟨hkpos, hkperiod, hkminimal⟩ hlperiod
  have hlk :=
    exists_mul_eq_of_isLeastUniformPeriod
      f l k ⟨hlpos, hlperiod, hlminimal⟩ hkperiod
  obtain ⟨q, hq⟩ := hkl
  obtain ⟨r, hr⟩ := hlk
  have hkle : k ≤ l :=
    Nat.le_of_dvd hlpos ⟨q, hq⟩
  have hlke : l ≤ k :=
    Nat.le_of_dvd hkpos ⟨r, hr⟩
  omega

theorem exists_uniform_period_of_injective_finite
    {W : Type} [Fintype W] (f : W → W)
    (hf : Function.Injective f) :
    ∃ k : Nat, 0 < k ∧
      ∀ w, functionIterate f k w = w := by
  classical

  let nFun : Nat := Fintype.card (W → W)

  let g : Fin (nFun + 1) → (W → W) :=
    fun i x => functionIterate f i.val x

  have hcollision : ∃ i j, i ≠ j ∧ g i = g j := by
    by_cases hcoll : ∃ i j, i ≠ j ∧ g i = g j
    · exact hcoll
    · have hg : Function.Injective g := by
        intro i j hij
        by_cases heq : i = j
        · exact heq
        · exact False.elim (hcoll ⟨i, j, heq, hij⟩)

      have hcard :
          Fintype.card (Fin (nFun + 1)) ≤
            Fintype.card (W → W) :=
        Fintype.card_le_of_injective g hg

      have hle : nFun + 1 ≤ nFun := by
        simpa only [Fintype.card_fin, nFun] using hcard

      omega

  obtain ⟨i, j, hne, hEq⟩ := hcollision

  have hval : i.val ≠ j.val := by
    intro hij
    exact hne (Fin.ext hij)

  by_cases hlt : i.val < j.val

  · let d := j.val - i.val

    have hdpos : 0 < d := by
      dsimp [d]
      omega

    have hdecomp : i.val + d = j.val := by
      dsimp [d]
      omega

    have hiterEq : ∀ x,
        functionIterate f i.val x =
        functionIterate f j.val x := by
      intro x
      change g i x = g j x
      exact congrFun hEq x

    refine ⟨d, hdpos, ?_⟩
    intro x

    have hprefix :
        functionIterate f i.val x =
        functionIterate f i.val
          (functionIterate f d x) := by
      calc
        functionIterate f i.val x =
            functionIterate f j.val x :=
          hiterEq x
        _ = functionIterate f (i.val + d) x := by
          rw [hdecomp]
        _ = functionIterate f i.val
            (functionIterate f d x) :=
          functionIterate_add f i.val d x

    exact
      (functionIterate_injective f hf i.val hprefix).symm

  · have hjlt : j.val < i.val := by
      omega

    let d := i.val - j.val

    have hdpos : 0 < d := by
      dsimp [d]
      omega

    have hdecomp : j.val + d = i.val := by
      dsimp [d]
      omega

    have hiterEq : ∀ x,
        functionIterate f j.val x =
        functionIterate f i.val x := by
      intro x
      change g j x = g i x
      exact (congrFun hEq x).symm

    refine ⟨d, hdpos, ?_⟩
    intro x

    have hprefix :
        functionIterate f j.val x =
        functionIterate f j.val
          (functionIterate f d x) := by
      calc
        functionIterate f j.val x =
            functionIterate f i.val x :=
          hiterEq x
        _ = functionIterate f (j.val + d) x := by
          rw [hdecomp]
        _ = functionIterate f j.val
            (functionIterate f d x) :=
          functionIterate_add f j.val d x

    exact
      (functionIterate_injective f hf j.val hprefix).symm

theorem exists_isLeastUniformPeriod_of_injective_finite
    {W : Type} [Fintype W] (f : W → W)
    (hf : Function.Injective f) :
    ∃ k : Nat, IsLeastUniformPeriod f k := by
  classical
  obtain ⟨k₀, hk₀pos, hk₀period⟩ :=
    exists_uniform_period_of_injective_finite f hf

  let P : Nat → Prop :=
    fun j => 0 < j ∧
      ∀ w, functionIterate f j w = w

  have hP : ∃ j, P j :=
    ⟨k₀, hk₀pos, hk₀period⟩

  let k := Nat.find hP
  have hk : P k := Nat.find_spec hP

  refine ⟨k, hk.1, hk.2, ?_⟩
  intro j hjpos hjlt hperiod
  have hPj : P j := ⟨hjpos, hperiod⟩
  have hkle : k ≤ j := Nat.find_min' hP hPj
  omega

theorem existsUnique_isLeastUniformPeriod_of_injective_finite
    {W : Type} [Fintype W] (f : W → W)
    (hf : Function.Injective f) :
    ∃! k : Nat, IsLeastUniformPeriod f k := by
  obtain ⟨k, hk⟩ :=
    exists_isLeastUniformPeriod_of_injective_finite f hf
  refine ⟨k, hk, ?_⟩
  intro l hl
  exact (isLeastUniformPeriod_unique f k l hk hl).symm

theorem confluent_functionGraph_iff_dvd_of_finite_injective
    {W : Type} [Fintype W] (f : W → W)
    (hf : Function.Injective f)
    (m n : Nat) :
    confluent (fun x y => y = f x) m n ↔
      ∃ k : Nat, IsLeastUniformPeriod f k ∧
        ∃ q : Nat, max m n - min m n = k * q := by
  obtain ⟨k, hk⟩ :=
    exists_isLeastUniformPeriod_of_injective_finite f hf
  constructor
  · intro hc
    refine ⟨k, hk, ?_⟩
    exact
      (confluent_functionGraph_iff_dvd_of_least_period
        f k m n hk).mp hc
  · rintro ⟨l, hl, q, hq⟩
    have heq : k = l :=
      isLeastUniformPeriod_unique f k l hk hl
    have hq' : max m n - min m n = k * q := by
      calc
        max m n - min m n = l * q := hq
        _ = k * q := by rw [← heq]
    exact
      (confluent_functionGraph_iff_dvd_of_least_period
        f k m n hk).mpr ⟨q, hq'⟩

theorem frameValid_functionGraph_iff_dvd_of_finite_injective
    {W : Type} [Fintype W] (f : W → W)
    (hf : Function.Injective f)
    (m n : Nat) :
    frameValid (fun x y => y = f x) m n ↔
      ∃ k : Nat, IsLeastUniformPeriod f k ∧
        ∃ q : Nat, max m n - min m n = k * q := by
  rw [generalized_confluence_correspondence
    (fun x y => y = f x) m n]
  exact confluent_functionGraph_iff_dvd_of_finite_injective
    f hf m n

def IsLeastPointPeriod
    {W : Type} (f : W → W) (w : W) (k : Nat) : Prop :=
  0 < k ∧
  functionIterate f k w = w ∧
  (∀ j : Nat, 0 < j → j < k →
    functionIterate f j w ≠ w)

theorem exists_mul_eq_of_isLeastPointPeriod
    {W : Type} (f : W → W)
    (w : W) (k d : Nat)
    (hleast : IsLeastPointPeriod f w k)
    (hperiod : functionIterate f d w = w) :
    ∃ q : Nat, d = k * q := by
  rcases hleast with ⟨hkpos, hkperiod, hminimal⟩
  have hdecomp : d % k + k * (d / k) = d :=
    Nat.mod_add_div d k
  have hrem : functionIterate f (d % k) w = w := by
    have hdw := hperiod
    rw [← hdecomp, functionIterate_add] at hdw
    have hmult :=
      functionIterate_mul_eq_self f k w hkperiod (d / k)
    rw [hmult] at hdw
    exact hdw
  by_cases hr : d % k = 0
  · have hd : d = k * (d / k) := by
      calc
        d = d % k + k * (d / k) := hdecomp.symm
        _ = k * (d / k) := by rw [hr]; simp
    exact ⟨d / k, hd⟩
  · have hrpos : 0 < d % k := Nat.pos_of_ne_zero hr
    have hrlt : d % k < k := Nat.mod_lt d hkpos
    exact False.elim (hminimal (d % k) hrpos hrlt hrem)

theorem exists_isLeastPointPeriod_of_injective_finite
    {W : Type} [Fintype W] (f : W → W)
    (hf : Function.Injective f) (w : W) :
    ∃ k : Nat, IsLeastPointPeriod f w k := by
  classical
  obtain ⟨k₀, hk₀pos, hk₀period⟩ :=
    exists_uniform_period_of_injective_finite f hf

  let P : Nat → Prop :=
    fun j => 0 < j ∧ functionIterate f j w = w

  have hP : ∃ j, P j :=
    ⟨k₀, hk₀pos, hk₀period w⟩

  let k := Nat.find hP
  have hk : P k := Nat.find_spec hP

  refine ⟨k, hk.1, hk.2, ?_⟩
  intro j hjpos hjlt hjperiod
  have hPj : P j := ⟨hjpos, hjperiod⟩
  have hkle : k ≤ j := Nat.find_min' hP hPj
  omega


theorem pointPeriod_dvd_globalPeriod
    {W : Type} (f : W → W)
    (w : W) (p k : Nat)
    (hpoint : IsLeastPointPeriod f w p)
    (hglobal : IsLeastUniformPeriod f k) :
    ∃ q : Nat, k = p * q := by
  rcases hglobal with ⟨hkpos, hkperiod, hkminimal⟩
  exact exists_mul_eq_of_isLeastPointPeriod
    f w p k hpoint (hkperiod w)

theorem uniformPeriod_of_pointwisePeriod_dvd
    {W : Type} (f : W → W)
    (p : W → Nat) (d : Nat)
    (hpoint : ∀ w, IsLeastPointPeriod f w (p w))
    (hdiv : ∀ w, ∃ q : Nat, d = p w * q) :
    ∀ w, functionIterate f d w = w := by
  intro w
  obtain ⟨q, hq⟩ := hdiv w
  rw [hq]
  exact functionIterate_mul_eq_self f (p w) w
    (hpoint w).2.1 q


theorem confluent_reflexive_symmetric_iff
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (m n : Nat) :
    confluent R m n ↔
      m + n ≥ 2 ∨
      (m + n ≥ 1 ∧
        (∀ x y z, R x y → R y z → R x z)) ∨
      (∀ x y, R x y → x = y) := by
  constructor
  · intro hConf
    by_cases htwo : m + n ≥ 2
    · exact Or.inl htwo
    · by_cases hone : m + n ≥ 1
      · right
        left
        constructor
        · exact hone
        · have hsum : m + n = 1 := by omega
          have hmn :
              (m = 0 ∧ n = 1) ∨
              (m = 1 ∧ n = 0) := by omega
          intro x y z hxy hyz
          rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · obtain ⟨t, hxt, hzt⟩ :=
              hConf y x z (hsym x y hxy) hyz
            have hxt' : x = t :=
              (relPow_zero_iff R x t).mp hxt
            have hzt' : R z t :=
              (relPow_one_iff R z t).mp hzt
            subst t
            exact hsym z x hzt'
          · obtain ⟨t, hxt, hzt⟩ :=
              hConf y x z (hsym x y hxy) hyz
            have hzt' : z = t :=
              (relPow_zero_iff R z t).mp hzt
            have hxt' : R x t :=
              (relPow_one_iff R x t).mp hxt
            subst t
            exact hxt'
      · right
        right
        have hm : m = 0 := by omega
        have hn : n = 0 := by omega
        subst m
        subst n
        exact
          (confluent_zero_zero_iff_eq_relation
            R href).mp hConf

  · intro h
    rcases h with htwo | hrest
    · exact
        confluent_of_reflexive_symmetric_of_sum_ge_two
          R href hsym m n htwo
    · rcases hrest with ⟨hone, htrans⟩ | hId
      · exact
          confluent_of_reflexive_symmetric_transitive_of_sum_ge_one
            R href hsym htrans m n hone
      · intro w v u hwv hwu
        have hv : v = w := (hId w v hwv).symm
        have hu : u = w := (hId w u hwu).symm
        subst v
        subst u
        exact ⟨w,
          relPow_refl_of_reflexive R href m w,
          relPow_refl_of_reflexive R href n w⟩


theorem frameValid_reflexive_symmetric_iff
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (m n : Nat) :
    frameValid R m n ↔
      m + n ≥ 2 ∨
      (m + n ≥ 1 ∧
        (∀ x y z, R x y → R y z → R x z)) ∨
      (∀ x y, R x y → x = y) := by
  rw [generalized_confluence_correspondence R m n]
  exact confluent_reflexive_symmetric_iff
    R href hsym m n


theorem confluent_reflexive_symmetric_nontransitive_iff
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (hnottrans :
      ¬ (∀ x y z, R x y → R y z → R x z))
    (m n : Nat) :
    confluent R m n ↔ m + n ≥ 2 := by
  rw [confluent_reflexive_symmetric_iff R href hsym m n]
  constructor
  · intro h
    rcases h with htwo | hrest
    · exact htwo
    · rcases hrest with ⟨_, htrans⟩ | hId
      · exact False.elim (hnottrans htrans)
      · apply False.elim
        apply hnottrans
        intro x y z hxy hyz
        have hxy' : x = y := hId x y hxy
        subst y
        exact hyz
  · exact Or.inl


theorem confluent_reflexive_symmetric_transitive_nonidentity_iff
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (hnontrivial : ∃ x y, R x y ∧ x ≠ y)
    (m n : Nat) :
    confluent R m n ↔ m + n ≥ 1 := by
  rw [confluent_equivalence_relation_iff
    R href hsym htrans m n]
  constructor
  · intro h
    rcases h with hpos | hId
    · exact hpos
    · obtain ⟨x, y, hxy, hne⟩ := hnontrivial
      exact False.elim (hne (hId x y hxy))
  · intro h
    exact Or.inl h


theorem frameValid_reflexive_symmetric_nontransitive_iff
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (hnottrans :
      ¬ (∀ x y z, R x y → R y z → R x z))
    (m n : Nat) :
    frameValid R m n ↔ m + n ≥ 2 := by
  rw [generalized_confluence_correspondence R m n]
  exact
    confluent_reflexive_symmetric_nontransitive_iff
      R href hsym hnottrans m n


theorem frameValid_reflexive_symmetric_transitive_nonidentity_iff
    {W : Type} (R : W → W → Prop)
    (href : ∀ x, R x x)
    (hsym : ∀ x y, R x y → R y x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (hnontrivial : ∃ x y, R x y ∧ x ≠ y)
    (m n : Nat) :
    frameValid R m n ↔ m + n ≥ 1 := by
  rw [generalized_confluence_correspondence R m n]
  exact
    confluent_reflexive_symmetric_transitive_nonidentity_iff
      R href hsym htrans hnontrivial m n

theorem functionGraph_reflexive_iff_identity
    {W : Type} (f : W → W) :
    (∀ x, x = f x) ↔ f = id := by
  constructor
  · intro h
    funext x
    exact (h x).symm
  · intro h x
    have hx : f x = id x := congrFun h x
    simpa using hx.symm

end GeneralizedConfluence
