def Relation (α : Sort u) := α → α → Prop
structure DecidableRelation (α : Sort u) :=
  rel: Relation α
  dec: DecidableRel rel
-- structure RelationOn (α β : Sort u) (f : α → β)
--   rel : Relation α

namespace Relation
def is_trans (r : Relation α) := ∀a b c, r a b → r b c → r a c
def is_refl (r : Relation α) := ∀a, r a a
def is_symm (r : Relation α) := ∀a b, r a b → r b a
def is_antisymm (r : Relation α) := ∀a b, r a b → r b a → a = b
def is_total (r : Relation α) := ∀a b, r a b ∨ r b a
def is_trichotomy (r : Relation α) := ∀a b,
    (a = b ∧ ¬r a b ∧ ¬r b a)
  ∨ (¬a = b ∧ r a b ∧ ¬r b a)
  ∨ (¬a = b ∧ ¬r a b ∧ r b a)

def is_equivalance (r : Relation α) := r.is_trans ∧ r.is_refl ∧ r.is_symm
def is_pre_ordered (r : Relation α) := r.is_trans ∧ r.is_refl
def is_partial_ordered (r : Relation α) := r.is_pre_ordered ∧ r.is_antisymm
def is_totally_ordered (r : Relation α) := r.is_partial_ordered ∧ r.is_total
def is_strictly_totally_ordered (r : Relation α) := r.is_trans ∧ r.is_trichotomy
end Relation


structure Voting :=
  -- 構成員の数
  n : Nat
  -- 選択肢の数
  m : Nat
  -- hn: 1 ≤ n
  hm: 3 ≤ m
namespace Voting
-- 構成員
def Member (v : Voting) := { k : Nat // k < v.n }
-- 選択肢
def Option (v : Voting) := { k : Nat // k < v.m }
-- 一人の投票の型
def Vote (_ : Voting) := { r : DecidableRelation Nat // r.rel.is_strictly_totally_ordered }
#check decide
namespace Vote
def default : Vote v := {
    val := ⟨fun x y => x < y, Nat.decLt⟩
    property := by
      apply And.intro
      . unfold Relation.is_trans
        intros
        apply Nat.lt_trans
        assumption
        assumption
      . unfold Relation.is_trichotomy
        intro a b
        cases Nat.lt_or_ge a b
        . apply Or.inr; apply Or.inl
          repeat (any_goals apply And.intro)
          . exact Nat.ne_of_lt ‹a < b›
          . assumption
          . show ¬b < a
            rw [Nat.not_lt_eq]
            exact Nat.le_of_lt ‹a < b›
        . rename_i h
          cases Nat.eq_or_lt_of_le h
          . apply Or.inl
            repeat (any_goals apply And.intro)
            . apply Eq.symm; assumption
            . show ¬a < b
              rw [Nat.not_lt_eq]
              assumption
            . show ¬b < a
              rw [Nat.not_lt_eq]
              apply Nat.le_of_eq ..
              apply Eq.symm
              assumption
          . apply Or.inr; apply Or.inr
            rename_i h
            repeat (any_goals apply And.intro)
            . apply Ne.symm
              apply Nat.ne_of_lt
              assumption
            . show ¬a < b
              rw [Nat.not_lt_eq]
              exact Nat.le_of_lt ‹b < a›
            . assumption
  }
instance : Inhabited (Vote v) where
  default := default
theorem eq_false (a b : α) [DecidableEq α] : ((a != b) = false) ↔ ((a == b) = true) := by
  sorry

-- 投票に対し，特定の x を最優先しつつ他を変更しない投票を作る
def prec_of (v : Vote vs) (x : Nat) : Vote vs := {
  val :=
    let rel_b := fun y z =>
      if y = x then z != x
      else if z = x then false
      else
        let {rel, dec} := v.val
        @decide (rel y z) (dec y z)
    {
      rel := fun x y => rel_b x y = true
      dec := fun x y =>
        if h : rel_b x y then
          Decidable.isTrue (by assumption)
        else
          Decidable.isFalse (by assumption)
    }
  property := by
    unfold Relation.is_strictly_totally_ordered
    simp
    repeat (any_goals apply And.intro)
    . unfold Relation.is_trans
      intro _ _ _ h1 h2
      repeat any_goals (
        first | split at h1 | split at h2 | simp at h1 | simp at h2 | simp | split
        try first | assumption | contradiction
      )
      apply v.property.left
      assumption
      assumption
    . unfold Relation.is_trichotomy
      intro a b
      have h := v.property.right a b
      unfold Relation.is_trichotomy at h
      repeat any_goals (
        have h : Or .. := h
        cases h
        all_goals rename_i h
      )
      repeat any_goals (
        have h : And .. := h
        cases h
        all_goals rename_i h0 h
      )
      apply Or.inl
      repeat any_goals constructor
      repeat any_goals (
        first | simp | split | assumption | contradiction | trivial
      )
      . have : b = x := sorry
        have xx := eq_false b x
        have xxx := xx.mpr
        apply xxx


















      -- all_goals try (
      --   apply Or.inl
      --   repeat cases

      -- )

      -- all_goals (
      --   cases h with
      --   case inl h | inr h=>
      -- )

      -- apply Or.inl

      sorry
      -- split at h1
      -- all_goals (split at h2; split; assumption)

        -- rw [‹(a = x) = true›]
        -- try rw [‹(b = x) = true›]
        -- try rw [‹(c = x) = true›]
        -- try rw [‹(a != x) = true›]
        -- try rw [‹(b != x) = true›]
        -- try rw [‹(c != x) = true›]






}
end Vote
-- 全員の投票の型
def Votes (v : Voting) := v.Member → v.Vote
-- 部分集団
def Group (v : Voting) := v.Member → Bool
namespace Group
def size (g : Group v) : Nat :=
  let rec size' g k (h : k ≤ v.n) :=
    match k with
    | 0 => 0
    | k+1 =>
      let hk : k < v.n := calc
        k < k + 1 := Nat.lt_succ_self ..
        _ ≤ v.n := by assumption
      let hk' : k ≤ v.n := Nat.le_of_lt hk
      let i : v.Member := {
        val := k
        property := hk
      }
      let t := if g i then 1 else 0
      (size' g k hk') + t
  size' g v.n (Nat.le_refl ..)
def is_sub_of (g g' : Group v) := ∀i, g i → g' i
def is_sup_of (g g' : Group v) := ∀i, g' i → g i
def split (g : Group v) : 2 ≤ g.size → ∃g1 g2 : Group v,
  0 < g1.size ∧ 0 < g2.size ∧ g.is_sup_of g1 ∧ g.is_sup_of g2 := by
  sorry

end Group
end Voting

structure VotingSystem :=
  -- 社会
  v : Voting
  -- 全員の投票から一つの投票を作る関数
  f : v.Votes → v.Vote

namespace VotingSystem
-- 満場一致性 (Unanimity)
def unanimity (vs : VotingSystem) :=
  ∀x y : vs.v.Option, ∀votes : vs.v.Votes, (
    (
      ∀i : vs.v.Member,
      let r := (votes i).val
      r.rel x.val y.val
    )
    →
    (vs.f votes).val.rel x.val y.val
  )
-- 独立性 (Independence of irrelevant alternatives (IIA))
def iia (vs : VotingSystem) :=
  ∀x y : vs.v.Option, ∀votes1 votes2 : vs.v.Votes, (
    (
      ∀i : vs.v.Member,
      let r1 := (votes1 i).val
      let r2 := (votes2 i).val
      r1.rel x.val y.val ↔ r2.rel x.val y.val
    )
    →
    let R1 := (vs.f votes1).val
    let R2 := (vs.f votes2).val
    R1.rel x.val y.val ↔ R2.rel x.val y.val
  )
-- 集団gはx yについて決定権を持つ
def is_decisive (vs : VotingSystem) (g : vs.v.Group) (x y : vs.v.Option) :=
  ∀votes : vs.v.Votes,
    (
      ∀i : vs.v.Member,
        let r := (votes i).val
        g i →
        r.rel x.val y.val
    )
    →
    let R := (vs.f votes).val
    R.rel x.val y.val
-- 集団gはx yについて弱決定権を持つ
def is_weakly_decisive {vs : VotingSystem} (g : vs.v.Group) (x y : vs.v.Option) :=
  ∀votes : vs.v.Votes,
    (
      ∀i : vs.v.Member,
        let r := (votes i).val
        (g i → r.rel x.val y.val) ∧
        (¬ g i → r.rel y.val x.val)
    )
    →
    let R := (vs.f votes).val
    R.rel x.val y.val
-- 補題: 決定権を持つならば，弱決定権を持つ
theorem decisive_then_weakly_decisive {vs : VotingSystem} g x y:
  vs.is_decisive g x y → vs.is_weakly_decisive g x y := by
  intro h
  unfold is_decisive at h
  unfold is_weakly_decisive
  intro _ h' _
  apply h
  intro j r hg
  have h' := h' j
  cases h'
  rename_i left _
  apply left
  assumption
-- 補題: 特定のペアで弱決定権を持つ集団の存在性
theorem exists_weakly_decisive_sub (vs : VotingSystem) (hu: unanimity vs)
  : ∃g : vs.v.Group, ∃x y : vs.v.Option, is_weakly_decisive g x y := by
  exists (fun _ => true)
  let x : vs.v.Option := {
    val := 0
    property := by
      have _ := vs.v.hm
      calc
        0 < 3 := by trivial
        _ ≤ vs.v.m := by assumption
  }
  let y : vs.v.Option := {
    val := 1
    property := by
      have _ := vs.v.hm
      calc
        1 < 3 := by trivial
        _ ≤ vs.v.m := by assumption
  }
  exists x, y
  unfold is_weakly_decisive
  intro _ h _
  unfold unanimity at hu
  apply hu
  intro i
  have h := h i
  cases h
  rename_i left _
  apply left
  trivial
-- 決定権を持つ集団の収縮性
theorem e (vs : VotingSystem) (hiia : vs.iia) :
  ∀g : vs.v.Group, ∀x y, (
    2 ≤ g.size ∧ is_weakly_decisive g x y
    →
    ∃g' : vs.v.Group, ∃z w, g'.size < g.size ∧ is_weakly_decisive g' z w
  ) := by
  intro g x y ⟨h2, _⟩
  let ⟨g1, g2, _, _, _, _⟩ := g.split h2
  let votes : vs.v.Votes :=
    let val := fun i =>
      if g1 i then
        -- x < y < z < (others)
        Voting.Vote.default
      else if g2 i then
        -- z < x < y < (others)
        Voting.Vote.default
      else
        -- y < z < x < (others)
        Voting.Vote.default
    {
      val := val
      property := by sorry
    }
  done

end VotingSystem
