(*       This file presents the formal verification of concepts      *)
(*                  about equivalence classification.                *)
(*  It is developmented in the CoqIDE (version 8.13.2) for windows.  *)

(** equivalence_relation *)

Require Import mk.mk_theorems.

(* 自反性 *)
Definition Reflexivity R a := ∀ x, x ∈ a -> [x,x] ∈ R.

(* 定义: R在a上是对称的 *)
Definition Symmetry R a := ∀ x y, x ∈ a -> y ∈ a
  -> [x,y] ∈ R -> [y,x] ∈ R.

(* 定义: R在a上是传递的
        此定义MK中已有有, 此处再次强调 *)
Definition Transitivity R a := ∀ x y z, x ∈ a -> y ∈ a -> z ∈ a
  -> [x,y] ∈ R -> [y,z] ∈ R -> [x,z] ∈ R.

(* 定义: R是a上的等价关系. *)
Definition equRelation R a := R ⊂ a × a
  /\ Reflexivity R a /\ Symmetry R a /\ Transitivity R a.

(* 等价关系的一个简单实例: 恒等关系是任意a上的等价关系. *)
Example Example_equR : ∀ a, equRelation (\{\ λ u v, u ∈ a
  /\ v ∈ a /\ u = v \}\) a.
Proof.
  repeat split; intros.
  - unfold Included; intros. apply AxiomII in H
    as [H[x[y[H0[H1[]]]]]]. apply AxiomII; split; eauto.
  - unfold Reflexivity; intros. apply AxiomII'; repeat split; auto.
    apply MKT49a; eauto.
  - unfold Symmetry; intros. apply AxiomII' in H1 as [H1[H2[]]].
    apply AxiomII'; repeat split; auto.
    apply MKT49a; apply MKT49b in H1; tauto.
  - unfold Transitivity; intros. apply AxiomII' in H2 as [H2[H4[]]].
    apply AxiomII' in H3 as [H3[H7[]]].
    apply AxiomII'; repeat split; auto. apply MKT49b in H2 as [].
    apply MKT49b in H3 as []. apply MKT49a; auto.
    rewrite H6,H9; auto.
Qed.

(* 定义: 等价类, 关于 a上的等价关系R的以x为代表的 等价类.
        [注: 1.实际使用此定义时, 要求x为a的一个元, R为a上的一个等价关系.
             2.当R为一个等价关系时, 'xRy'除了原有的'x,y满足R关系'之意,
               也表达了'x与y是关于R等价的'. ] *)
Definition equClass x R a := \{ λ u, u ∈ a /\ [u,x] ∈ R \}.

(* 关于等价类的定理1: 相互等价的元素所代表的等价类相等. *)
Theorem equClassT1 : ∀ R a x y, equRelation R a -> x ∈ a -> y ∈ a
  -> [x,y] ∈ R <-> equClass x R a = equClass y R a.
Proof.
  split; intros.
  - destruct H as [H[H3[]]]. apply AxiomI; split; intros; apply
    AxiomII in H6 as [H6[]]; apply AxiomII; repeat split; auto.
    + apply (H5 z x y); auto.
    + apply H4 in H2; auto. apply (H5 z y x); auto.
  - assert (x ∈ (equClass y R a)).
    { rewrite <-H2. apply AxiomII.
      destruct H as [H[H3[]]]. split; eauto. }
    apply AxiomII in H3; tauto.
Qed.

(* 关于等价类的定理2: 不同的等价类没有公共元素. *)
Theorem equClassT2 : ∀ R a x y, equRelation R a -> x ∈ a -> y ∈ a
  -> equClass x R a <> equClass y R a
    <-> (equClass x R a) ∩ (equClass y R a) = Φ.
Proof.
  split; intros.
  - apply NNPP; intro. apply NEexE in H3 as [z].
    apply MKT4' in H3 as []. apply AxiomII in H3 as [H3[]].
    apply AxiomII in H4 as [H4[]]. pose proof H as H'.
    destruct H as [H[H9[]]]. apply H10 in H6; auto.
    apply (H11 x z y),(equClassT1 R a x y) in H8; auto.
  - intro. rewrite H3,MKT5' in H2. elim (@ MKT16 y).
    rewrite <-H2. apply AxiomII. destruct H as [H[]].
    repeat split; eauto.
Qed.

(* 定义: P是a的一个剖分(或叫做 分类),
        是指 1. P的元素均为a的子集.
            2. Φ不在P中.
            3. P的所有元素之并即为a.
            4. P中任意两元素相交是空.
        [注: P的作用在于将a不含公共元地分成若干子集]  *)
Definition Partition P a := P ⊂ pow(a) /\ Φ ∉ P /\ ∪P = a
  /\ (∀ x y, x ∈ P -> y ∈ P -> x <> y -> x ∩ y = Φ).

(* 定义: 商集, a上所有关于R的等价类组成的一个类.
        [注: 使用该定义时, R需是a上的一个等价关系. ] *)
Definition QuotientSet a R := \{ λ u, ∃ x, x ∈ a /\ u = equClass x R a \}.

Declare Scope eqr_scope.
Delimit Scope eqr_scope with eqr.
Open Scope eqr_scope.

Notation "a / R" := (QuotientSet a R) : eqr_scope.

(* 关于等价类的定理3: 每个等价关系下的商集都是一个剖分. *)
Theorem equClassT3 : ∀ a R, Ensemble a -> equRelation R a
  -> Partition (a/R) a.
Proof.
  intros. pose proof H.
  destruct H0 as [H0[H2[]]]. repeat split; intros.
  - unfold Included; intros. apply AxiomII in H5 as [H5[x[]]].
    rewrite H7. apply AxiomII.
    assert ((equClass x R a) ⊂ a).
    { unfold Included; intros. apply AxiomII in H8; tauto. }
    split; auto. apply (MKT33 a); auto.
  - intro. apply AxiomII in H5 as [H5[x[]]]. elim (@ MKT16 x).
    rewrite H7. apply AxiomII; repeat split; eauto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H5 as [H5[x[]]]. apply AxiomII in H7
      as [H7[x0[]]]. rewrite H9 in H6. apply AxiomII in H6; tauto.
    + apply AxiomII; split; eauto. exists (equClass z R a).
      split. apply AxiomII; repeat split; eauto. apply
      AxiomII. split; eauto. apply (MKT33 a); auto. unfold
      Included; intros. apply AxiomII in H6; tauto.
  - apply AxiomII in H5 as [H5[x1[]]].
    apply AxiomII in H6 as [H6[x2[]]].
    rewrite H9 in *. rewrite H11 in *.
    apply equClassT2; repeat split; auto.
Qed.


