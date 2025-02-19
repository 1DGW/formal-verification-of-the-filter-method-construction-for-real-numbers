(*    This file presents the formalization for construction of *Q.   *)
(*  It is developmented in the CoqIDE (version 8.13.2) for windows.  *)

(** Zs_to_Qs *)

Require Export fmcr.Ns_to_Zs.

(* 以下策略用于将引理中的“差”展开成为两个条件 *)
Lemma Z'split_Lemma : ∀ u, u ∈ (Z' ~ [Z'0]) -> u ∈ Z' /\ u <> Z'0.
Proof.
  intros. apply MKT4' in H as []. apply AxiomII in H0 as []. split; auto.
  intro; elim H1. apply MKT41; auto. pose proof Z'0_in_Z'; eauto.
Qed.

Ltac Z'split H := pose proof H as Ht; apply Z'split_Lemma in Ht as [].

(* 以下策略是对Z'split的拓展 *)
Lemma Z'split1_Lemma : (Z'_Z ~ [Z'0]) ⊂ (Z' ~ [Z'0]).
Proof.
  unfold Included; intros. apply MKT4' in H as [].
  apply MKT4'; split; auto. apply Z'_Z_subset_Z'; auto.
Qed.

Ltac Z'split1 H H1 := pose proof H as H1; apply Z'split1_Lemma in H1; Z'split H1.

(* *Z和*Z~[0]的笛卡尔乘积, *Q为笛卡尔乘积后的一个分类 *)
Definition Z'_De := Z' × (Z' ~ [Z'0]).

Property Z'_De_is_Set : Ensemble Z'_De.
Proof.
  apply MKT74; try apply Z'_is_Set; auto.
  apply (MKT33 Z'); try apply Z'_is_Set; auto.
  unfold Included; intros. apply MKT4' in H; tauto.
Qed.

(* 定义一个关系, 之后可以证明: 此关系为 *Z × ( *Z ~ [0] ) 上的等价关系. *)
Definition R_Z' := \{\ λ u v, ∃ a b c d, a ∈ Z'
  /\ b ∈ (Z' ~ [Z'0]) /\ c ∈ Z' /\ d ∈ (Z' ~ [Z'0])
  /\ u = [a,b] /\ v = [c,d] /\ a · d = b · c \}\.

(* 证明: 关系 R_Z' 为 *Z × ( *Z ~ [0] ) 上的等价关系. *)
Property R_Z'_is_equRelation : equRelation R_Z' Z'_De.
Proof.
  repeat split.
  - unfold Included; intros. apply AxiomII in H
    as [H[u[v[H0[a[b[c[d[H1[H2[H3[H4[H5[]]]]]]]]]]]]]].
    rewrite H0 in *. apply AxiomII'; split; auto.
    rewrite H5,H6. split; apply AxiomII'; split;
    try apply MKT49a; eauto.
  - unfold Reflexivity; intros. apply AxiomII in H as [H[m[n[H0[]]]]].
    apply AxiomII; split. apply MKT49a; auto. exists [m,n],[m,n]. rewrite H0.
    split; auto. exists m,n,m,n. repeat split; auto.
    apply Z'_Mult_Commutation; auto. apply MKT4' in H2; tauto.
  - unfold Symmetry; intros.
    apply AxiomII in H as [H[x0[y0[H2[]]]]].
    apply AxiomII in H0 as [H0[x1[y1[H5[]]]]].
    rewrite H2,H5 in *. apply AxiomII' in H1
    as [H1[a[b[c[d[H8[H9[H10[H11[H12[]]]]]]]]]]].
    rewrite H12,H13 in *. apply AxiomII'; split.
    apply MKT49a; apply MKT49b in H1; tauto.
    exists c,d,a,b. repeat split; auto.
    rewrite Z'_Mult_Commutation,(Z'_Mult_Commutation d);
    apply MKT4' in H9; apply MKT4' in H11; auto; try tauto.
  - unfold Transitivity; intros.
    apply AxiomII in H as [H[x0[y0[H4[]]]]].
    apply AxiomII in H0 as [H0[x1[y1[H7[]]]]].
    apply AxiomII in H1 as [H1[x2[y2[H10[]]]]].
    apply AxiomII' in H2
    as [H2[a0[b0[c0[d0[H13[H14[H15[H16[H17[]]]]]]]]]]].
    apply AxiomII' in H3
    as [H3[a1[b1[c1[d1[H20[H21[H22[H23[H24[]]]]]]]]]]].
    rewrite H4,H7,H10 in *. apply AxiomII';split.
    apply MKT49a; auto. exists a0,b0,c1,d1. repeat split; auto.
    rewrite H18 in H24. apply MKT55 in H24 as []; try split; eauto.
    rewrite H24,H27 in H19.
    assert ((a0 · b1) · (a1 · d1) = (b0 · a1) · (b1 · c1)).
    { rewrite H19,H26; auto. }
    Z'split H14. Z'split H21. Z'split H23.
    rewrite (Z'_Mult_Commutation a1),
    (Z'_Mult_Commutation b1),Z'_Mult_Association,
    Z'_Mult_Association,<-(Z'_Mult_Association b1),
    <-(Z'_Mult_Association a1),(Z'_Mult_Commutation b1),
    (Z'_Mult_Commutation a1),Z'_Mult_Association,
    Z'_Mult_Association,<-(Z'_Mult_Association a0),
    <-(Z'_Mult_Association b0),(Z'_Mult_Commutation b1),
    Z'_Mult_Commutation,(Z'_Mult_Commutation (b0 · c1))
    in H28; auto with Z'.
    destruct (classic (a1 = Z'0)).
    + rewrite H35,Z'_Mult_Commutation,Z'_Mult_Property1 in H26;
      auto with Z'. symmetry in H26.
      apply Z'_Mult_Property3 in H26 as []; try contradiction; auto.
      rewrite H35,Z'_Mult_Property1 in H19; auto.
      apply Z'_Mult_Property3 in H19 as []; try contradiction; auto.
      rewrite H19,H26,Z'_Mult_Commutation,Z'_Mult_Property1,
      Z'_Mult_Property1; auto with Z'.
    + apply Z'_Mult_Cancellation in H28; auto with Z'. intro.
      apply Z'_Mult_Property3 in H36 as []; auto.
Qed.

Declare Scope q'_scope.
Delimit Scope q'_scope with q'.
Open Scope q'_scope.

Notation "\[ u \] " := (equClass u R_Z' Z'_De)(at level 5) : q'_scope.

(* 证明: [(a,b)] = [(c,d)] 即 a*d = b*c. *)
Property R_Z'_Property : ∀ a b c d,
  a ∈ Z' -> b ∈ (Z' ~ [Z'0]) -> c ∈ Z' -> d ∈ (Z' ~ [Z'0])
  -> \[[a,b]\] = \[[c,d]\] <-> a · d = b · c.
Proof.
  split; intros.
  - apply equClassT1 in H3; try apply R_Z'_is_equRelation; auto.
    apply AxiomII' in H3
    as [H3[a0[b0[c0[d0[H4[H5[H6[H7[H8[]]]]]]]]]]].
    apply MKT55 in H8 as []; try split; eauto.
    apply MKT55 in H9 as []; try split; eauto.
    rewrite H8,H9,H11,H12; auto.
    apply AxiomII'; split; try apply MKT49a; eauto.
    apply AxiomII'; split; try apply MKT49a; eauto.
  - apply equClassT1; try apply R_Z'_is_equRelation; auto;
    try apply AxiomII'; try split; try apply MKT49a; try apply MKT49a; eauto.
    exists c,d,a,b; repeat split; auto. Z'split H0. Z'split H2.
    rewrite Z'_Mult_Commutation,(Z'_Mult_Commutation d); auto.
Qed.

(* 定义: *Q 为 *Z × ( *Z ~ [0] ) 关于 R_Z' 的商集. *)
Definition Q' := Z'_De / R_Z'.

(* *Q是一个集 *)
Property Q'_is_Set : Ensemble Q'.
Proof.
  apply (MKT33 (pow(Z'_De))); try apply MKT38a,Z'_De_is_Set; auto.
  unfold Included; intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII; split; auto. rewrite H1. unfold Included; intros.
  apply AxiomII in H2; tauto.
Qed.

Property Q'_Instantiate1 : ∀ u, u ∈ Q'
  -> ∃ a b, a ∈ Z' /\ b ∈ (Z' ~ [Z'0]) /\ b ∈ Z' /\ b <> Z'0 /\ u = \[[a,b]\].
Proof.
  intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII in H0 as [H0[a[b[H2[]]]]]. exists a,b. rewrite H1,H2.
  repeat split; auto; apply MKT4' in H4 as []; auto. intro.
  apply AxiomII in H5 as []. elim H7. apply MKT41; auto.
  pose proof Z'0_in_Z'. eauto.
Qed.

Property Q'_Instantiate2 : ∀ a b, a ∈ Z' -> b ∈ (Z' ~ [Z'0])
  -> \[[a,b]\] ∈ Q'.
Proof.
  intros. assert (Ensemble (\[[a,b]\])).
  { apply (MKT33 Z'_De). apply MKT74. apply Z'_is_Set.
    apply (MKT33 Z'). apply Z'_is_Set.
    unfold Included; intros. apply MKT4' in H1; tauto.
    unfold Included; intros. apply AxiomII in H1; tauto. }
  apply AxiomII; split; auto. exists ([a,b]). split; auto.
  apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Ltac inQ' H a b := apply Q'_Instantiate1 in H as [a[b[?[?[?[]]]]]].

(* 定义一个新的类, 之后的证明可见, 此类实际为*Q上的'零元'. *)
Definition Q'0 := \{\ λ u v, u = Z'0 /\ v ∈ (Z' ~ [Z'0]) \}\.

(* 定义一个新的类, 之后的证明可见, 此类实际为*Q上的'幺元(单位元)'. *)
Definition Q'1 := \{\ λ u v, v ∈ (Z' ~ [Z'0]) /\ u = v \}\.

(* Q'0 = [0,1]代表的等价类. [注: 这里的0是指*Z中的零元, 1指*Z中的幺元.] *)
Property Q'0_Property : Q'0 = \[[Z'0,Z'1]\].
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[a[b[H0[]]]]]. Z'split H2.
    apply AxiomII; split; auto. rewrite H0,H1. split.
    + apply AxiomII'; repeat split; auto with Z'. rewrite <-H1,<-H0; auto.
    + apply AxiomII'; split. apply MKT49a. rewrite <-H1,<-H0; auto.
      pose proof Z'0_in_Z'. pose proof Z'1_in_Z'. apply MKT49a; eauto.
      exists Z'0,b,Z'0,Z'1. repeat split; auto with Z'.
      rewrite Z'_Mult_Commutation,Z'_Mult_Property1,Z'_Mult_Property1; auto with Z'.
  - apply AxiomII in H as [H[]].
    apply AxiomII in H0 as [H0[x[y[H2[]]]]]. rewrite H2 in *.
    apply AxiomII' in H1 as [H1[a[b[c[d[H5[H6[H7[H8[H9[]]]]]]]]]]].
    apply MKT55 in H9 as []; apply MKT49b in H as []; auto.
    apply MKT55 in H10 as []; apply MKT49b in H1 as [];
    apply MKT49b in H15 as []; auto. apply AxiomII'; split; auto.
    rewrite H12. split; auto. rewrite <-H9,<-H10,<-H14,
    Z'_Mult_Property1,Z'_Mult_Property2 in H11; auto with Z'.
    apply MKT4' in H6; tauto.
Qed.

(* 验证: Q'0 确实是Q'中的元素 *)
Property Q'0_in_Q' : Q'0 ∈ Q'.
Proof.
  pose proof Q'0_Property. pose proof Z'0_in_Z'. pose proof Z'1_in_Z'.
  rewrite H. apply Q'_Instantiate2; auto. apply MKT4'; split; auto.
  apply AxiomII; split; eauto. intro. apply MKT41 in H2; eauto.
  elim Z'0_isnot_Z'1; auto.
Qed.

Global Hint Resolve Q'0_in_Q' : Q'.

(* Q'1 = [1,1]代表的等价类. [注: 这里的1是指*Z中的幺元. ]      *)
Property Q'1_Property : Q'1 = \[[Z'1,Z'1]\].
Proof.
  pose proof Z'1_in_Z'. apply AxiomI; split; intros.
  - apply AxiomII in H0 as [H0[u[v[H1[]]]]]. rewrite H1,H3 in *.
    Z'split H2. apply AxiomII; repeat split; try apply AxiomII'; auto.
    split. apply MKT49a; auto. apply MKT49a; eauto. exists v,v,Z'1,Z'1.
    repeat split; auto. apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H6. elim Z'0_isnot_Z'1; auto.
    pose proof Z'0_in_Z'; eauto.
  - apply AxiomII in H0 as [H0[]]. apply AxiomII in H1 as [H1[x[y[H3[]]]]].
    rewrite H3 in *. apply AxiomII' in H2
    as [H2[a[b[c[d[H6[H7[H8[H9[H10[]]]]]]]]]]].
    apply MKT55 in H11 as []; try split; eauto. rewrite <-H11,<-H13 in H12.
    Z'split H7. rewrite Z'_Mult_Property2,Z'_Mult_Property2 in H12; auto.
    rewrite H10,H12 in *. apply AxiomII'; auto.
Qed.

(* 验证: Q'1 确实是Q'中的元素 *)
Property Q'1_in_Q' : Q'1 ∈ Q'.
Proof.
  pose proof Q'1_Property. pose proof Z'0_in_Z'. pose proof Z'1_in_Z'.
  rewrite H. apply Q'_Instantiate2; auto. apply MKT4'; split; auto.
  apply AxiomII; split; eauto. intro. apply MKT41 in H2; eauto.
  elim Z'0_isnot_Z'1; auto.
Qed.

Global Hint Resolve Q'1_in_Q' : Q'.

(* 验证 *Q中的性质(零元和幺元不相等) *)
Property Q'0_isnot_Q'1 : Q'0 <> Q'1.
Proof.
  intros; intro. rewrite Q'0_Property,Q'1_Property in H; auto.
  apply R_Z'_Property in H; auto with Z'.
  rewrite Z'_Mult_Property2,Z'_Mult_Property2 in H; auto with Z'.
  elim Z'0_isnot_Z'1; auto.
Qed.

(* 定义 *Q上的序关系  *Q上的u和v, u前于v就是说, 所有 可以代表u的[a,b] 和
                   所有 可以代表v的[c,d] (其中b,d需要大于0) 都要满足:  a*d 前于 b*c
                   [注: b,d要求大于0是因为Z'中存在小于0的负数,负数会导致序的方向改变.
                      例如:
                           按照*Q上的序关系, [1,2] 前于 [2,3]
                           同时有: [-1,-2]=[1,2]
                           但此时: 根据序关系的定义会得出 [2,3] 前于 [-1,-2] .]    *)
Definition Q'_Ord := \{\ λ u v, ∀ a b c d, a ∈ Z' -> b ∈ (Z' ~ [Z'0])
  -> c ∈ Z' -> d ∈ (Z' ~ [Z'0]) -> Z'0 < b -> Z'0 < d
  -> u = \[[a,b]\] -> v = \[[c,d]\] -> (a · d) < (b · c) \}\.

Notation "u < v" := ([u,v] ∈ Q'_Ord) : q'_scope.

(* 验证  *Q上序关系的定义的合理性: 所规定的序关系 与 表示元素的代表 无关.
        若 [a,b] = [a1,b1]   [c,d] = [c1,d1]  (指等价类相同) (其中b,b1,d,d1均大于0)
        则  a*d  *Z前于  b*c    就等价于    a1*d1  *Z前于  b1*c1
        [注: 实际上就是要验证: 序关系与表示同一元素的代表的选择无关. ] *)
Property Q'_Ord_Reasonable : ∀ a b c d a1 b1 c1 d1,
  a ∈ Z' -> b ∈ (Z' ~ [Z'0]) -> c ∈ Z' -> d ∈ (Z' ~ [Z'0])
  -> a1 ∈ Z' -> b1 ∈ (Z' ~ [Z'0]) -> c1 ∈ Z' -> d1 ∈ (Z' ~ [Z'0])
  -> \[[a,b]\] = \[[a1,b1]\] -> \[[c,d]\] = \[[c1,d1]\]
  -> (Z'0 < b)%z' -> (Z'0 < d)%z' -> (Z'0 < b1)%z' -> (Z'0 < d1)%z'
  -> ((a · d) < (b · c) <-> (a1 · d1) < (b1 · c1))%z'.
Proof.
  intros. Z'split H0; Z'split H2; Z'split H4; Z'split H6.
  apply R_Z'_Property in H7; auto. apply R_Z'_Property in H8; auto.
  assert ((b1 · d1) · (a · d) = (b · d) · (a1 · d1)).
  { rewrite Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association d1),<-(Z'_Mult_Association d),
    (Z'_Mult_Commutation d1),(Z'_Mult_Commutation d),
    Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association b1),<-(Z'_Mult_Association b),
    (Z'_Mult_Commutation b1),(Z'_Mult_Commutation d1),H7; auto with Z'. }
  assert ((b1 · d1) · (b · c) = (b · d) · (b1 · c1)).
  { rewrite Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association d1),<-(Z'_Mult_Association d),
    (Z'_Mult_Commutation d1),(Z'_Mult_Commutation d),
    Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association b1),<-(Z'_Mult_Association b),
    (Z'_Mult_Commutation b1),(Z'_Mult_Commutation d1),H8; auto with Z'. }
  split; intros.
  - apply (Z'_Mult_PrOrder _ _ (b1 · d1)) in H23; auto with Z'.
    rewrite H21,H22 in H23. apply Z'_Mult_PrOrder in H23; auto with Z'.
  - apply (Z'_Mult_PrOrder _ _ (b · d)) in H23; auto with Z'.
    rewrite <-H22,<-H21 in H23. apply Z'_Mult_PrOrder in H23; auto with Z'.
Qed.

(* *Q上序关系的实例化描述: 
               [a,b]  *Q前于  [c,d]   (指等价类前于)
        就是指   a*d   *Z前于   b*c    (a b c d 都是*Z中的元, 且b,d大于0)   *)
Property Q'_Ord_Instantiate : ∀ a b c d, a ∈ Z' -> b ∈ (Z' ~ [Z'0])
  -> c ∈ Z' -> d ∈ (Z' ~ [Z'0]) -> (Z'0 < b)%z' -> (Z'0 < d)%z'
  -> \[[a,b]\] < \[[c,d]\] <-> ((a · d) < (b · c))%z'.
Proof.
  split; intros.
  - apply AxiomII' in H5 as []. apply H6; auto.
  - assert (\[[a,b]\] ∈ Q'). { apply Q'_Instantiate2; auto. }
    assert (\[[c,d]\] ∈ Q'). { apply Q'_Instantiate2; auto. }
    apply AxiomII'; split. apply MKT49a; eauto. intros.
    apply R_Z'_Property in H14; auto. apply R_Z'_Property in H15; auto.
    Z'split H0. Z'split H2. Z'split H9. Z'split H11.
    assert ((b0 · d0) · (a · d) = (b · d) · (a0 · d0)).
    { rewrite Z'_Mult_Association,Z'_Mult_Association,
      <-(Z'_Mult_Association d0),<-(Z'_Mult_Association d),
      (Z'_Mult_Commutation d0),(Z'_Mult_Commutation d),
      Z'_Mult_Association,Z'_Mult_Association,
      <-(Z'_Mult_Association b0),<-(Z'_Mult_Association b),
      (Z'_Mult_Commutation b0),(Z'_Mult_Commutation d0),H14; auto with Z'. }
    assert ((b0 · d0) · (b · c) = (b · d) · (b0 · c0)).
    { rewrite Z'_Mult_Association,Z'_Mult_Association,
      <-(Z'_Mult_Association d0),<-(Z'_Mult_Association d),
      (Z'_Mult_Commutation d0),(Z'_Mult_Commutation d),
      Z'_Mult_Association,Z'_Mult_Association,
      <-(Z'_Mult_Association b0),<-(Z'_Mult_Association b),
      (Z'_Mult_Commutation b0),(Z'_Mult_Commutation d0),H15; auto with Z'. }
    apply (Z'_Mult_PrOrder _ _ (b · d)); auto with Z'.
    rewrite <-H24,<-H25. apply Z'_Mult_PrOrder; auto with Z'.
Qed.

(*-------------  以下策略用于为等价类换代表, 以便于一些证明过程实现  --------------*)
Open Scope z'_scope.

Lemma Q'_equClass_alter : ∀ a b c, a ∈ Z' -> b ∈ (Z' ~ [Z'0])
  -> c ∈ (Z' ~ [Z'0]) -> (\[[a,b]\] = \[[(c · a),(c · b)]\])%q'.
Proof.
  intros. Z'split H0. Z'split H1. apply R_Z'_Property; auto with Z'.
  rewrite <-Z'_Mult_Association,(Z'_Mult_Commutation b),
  (Z'_Mult_Commutation a c); auto with Z'.
Qed.

Ltac Q'altH H a b x := try rewrite (Q'_equClass_alter a b x) in H; auto with Z'.

Ltac Q'alt a b x := try rewrite (Q'_equClass_alter a b x); auto with Z'.

Close Scope z'_scope.
(*----------------------------------------------------------------*)

Property Q'0_lt_Q'1 : Q'0 < Q'1.
Proof.
  rewrite Q'0_Property,Q'1_Property; auto.
  apply Q'_Ord_Instantiate; auto with Z'.
  rewrite Z'_Mult_Property2,Z'_Mult_Property2; auto with Z'.
Qed.

Global Hint Resolve Q'0_lt_Q'1 : Q'.

(* *Q上定义的 Q'_Ord关系 具有反自反性. *)
Property Q'_Ord_irReflex : ∀ u v, u ∈ Q' -> v ∈ Q' -> u = v -> ~ u < v.
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. rewrite H5,H9 in *.
  Q'altH H1 a b b. Q'altH H1 c d d. Q'alt a b b. Q'alt c d d.
  apply R_Z'_Property in H1; auto with Z'. intro.
  apply Q'_Ord_Instantiate in H10; auto with Z'. rewrite H1 in H10.
  elim (Z'_Ord_irReflex ((b · b) · (d · c)) ((b · b) · (d · c))); auto with Z'.
  Close Scope z'_scope.
Qed.

(* *Q上定义的 Q'_Ord关系 具有可传递性.  *)
Property Q'_Ord_Trans : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q'
  -> u < v -> v < w -> u < w.
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. inQ' H1 e f. Q'altH H7 a b b.
  Q'altH H11 c d d. Q'altH H15 e f f. rewrite H7,H11,H15 in *.
  apply Q'_Ord_Instantiate in H2; auto with Z'.
  apply Q'_Ord_Instantiate in H3; auto with Z'.
  apply Q'_Ord_Instantiate; auto with Z'.
  apply (Z'_Mult_PrOrder _ _ (f · f)) in H2; auto with Z'.
  apply (Z'_Mult_PrOrder _ _ (b · b)) in H3; auto with Z'.
  rewrite <-(Z'_Mult_Association (b · b)),
  (Z'_Mult_Commutation _ (f · f)) in H3; auto with Z'.
  apply (Z'_Ord_Trans ((f · f) · ((b · a) · (d · d)))) in H3; auto with Z'.
  rewrite (Z'_Mult_Commutation (b · a)),<-(Z'_Mult_Association (f · f)),
  <-(Z'_Mult_Association (b · b)),(Z'_Mult_Commutation (f · f)),
  (Z'_Mult_Commutation (b · b)),(Z'_Mult_Association (d · d)),
  (Z'_Mult_Association (d · d)),(Z'_Mult_Commutation (f · f)) in H3; auto with Z'.
  apply Z'_Mult_PrOrder in H3; auto with Z'.
  Close Scope z'_scope.
Qed.

(* *Q上定义的 Q'_Ord关系 满足三分律, 也就是 Q'_Ord连接*Q.  *)
Property Q'_Ord_Tri : Connect Q'_Ord Q'.
Proof.
  Open Scope z'_scope.
  intros. unfold Connect; intros. inQ' H a b. inQ' H0 c d.
  Q'altH H4 a b b. Q'altH H8 c d d. rewrite H4,H8.
  assert (((b · a) · (d · d)) ∈ Z' /\ ((d · c) · (b · b)) ∈ Z') as [].
  { split; auto with Z'. }
  apply (Z'_Ord_Tri _ ((d · c) · (b · b))) in H9; auto; clear H10.
  destruct H9 as [H9|[|]]; [left|right; left|repeat right];
  try apply Q'_Ord_Instantiate; try apply R_Z'_Property; auto with Z'.
  - rewrite (Z'_Mult_Commutation (b · b)); auto with Z'.
  - rewrite (Z'_Mult_Commutation (d · d)); auto with Z'.
  - rewrite (Z'_Mult_Commutation (b · b)); auto with Z'.
  Close Scope z'_scope.
Qed.

(* 定义: *Q上的加法, u + v 就是说   任意一个和u相等的等价类[(a,b)]
                             和 任意一个和v相等的等价类[(c,d)] 做运算,
                         运算结果为等价类[(ad+bc , bd)].   *)
Definition Q'_Plus u v := ∩(\{ λ w, ∀ a b c d, a ∈ Z' -> b ∈ (Z' ~ [Z'0])
  -> c ∈ Z' -> d ∈ (Z' ~ [Z'0]) -> u = \[[a,b]\] -> v = \[[c,d]\]
  -> w = \[[((a · d) + (b · c))%z',(b · d)%z']\] \}).

Notation "u + v" := (Q'_Plus u v) : q'_scope.

(* 验证 *Q中定义的加法运算的合理性: 对于任意*Q中的u和v, *Q上的加法定义中的{}中只有
                               一个元素, 并且该唯一的元素也在*Q中, 于是u与v的
                               相加结果形如 ∩[w] 是属于*Q且唯一的.        *)
Corollary Q'_Plus_Reasonable : ∀ u v, u ∈ Q' -> v ∈ Q'
  -> ∃ w, w ∈ Q' /\ [w] = \{ λ w, ∀ a b c d, a ∈ Z' -> b ∈ (Z' ~ [Z'0])
    -> c ∈ Z' -> d ∈ (Z' ~ [Z'0]) -> u = \[[a,b]\] -> v = \[[c,d]\]
    -> w = \[[((a · d) + (b · c))%z', (b · d)%z']\] \}.
Proof.
  intros. inQ' H a b. inQ' H0 c d.
  exists (\[[((a · d) + (b · c))%z',(b · d)%z']\]).
  assert ((\[[((a · d) + (b · c))%z',(b · d)%z']\]) ∈ Q').
  { apply Q'_Instantiate2; auto with Z'. }
  split; auto. apply AxiomI; split; intros.
  - apply MKT41 in H10; eauto. apply AxiomII; split.
    rewrite H10; eauto. intros. rewrite H10. Z'split H12. Z'split H14.
    assert ((b · d) ∈ (Z' ~ [Z'0]) /\ (b0 · d0) ∈ (Z' ~ [Z'0]))%z' as [].
    { split; auto with Z'. }
    apply R_Z'_Property; auto with Z'. rewrite H4 in H15.
    rewrite H8 in H16. apply R_Z'_Property in H15; auto.
    apply R_Z'_Property in H16; auto.
    rewrite Z'_Mult_Commutation,Z'_Mult_Distribution,Z'_Mult_Distribution,
    (Z'_Mult_Commutation (b0 · d0)%z'),(Z'_Mult_Commutation (b0 · d0)%z'),
    (Z'_Mult_Commutation a),Z'_Mult_Association,<-(Z'_Mult_Association a),H15,
    Z'_Mult_Association,<-(Z'_Mult_Association d),(Z'_Mult_Commutation d),
    (Z'_Mult_Association b c),(Z'_Mult_Commutation b0),<-(Z'_Mult_Association c),
    H16,(Z'_Mult_Association d c0),<-(Z'_Mult_Association b),
    (Z'_Mult_Commutation c0); auto with Z'.
  - apply AxiomII in H10 as []. apply MKT41; eauto.
Qed.

Property Q'_Plus_Instantiate : ∀ a b c d, a ∈ Z' -> b ∈ (Z' ~ ([Z'0]))
  -> c ∈ Z' -> d ∈ (Z' ~ ([Z'0])) -> \[[a,b]\] + \[[c,d]\]
    = \[[((a · d) + (b · c))%z',(b · d)%z']\].
Proof.
  intros. assert (\[[a,b]\] ∈ Q'). { apply Q'_Instantiate2; auto. }
  assert (\[[c,d]\] ∈ Q'). { apply Q'_Instantiate2; auto. } pose proof H3.
  apply (Q'_Plus_Reasonable (\[[a,b]\]) (\[[c,d]\])) in H5 as [x[]]; auto.
  unfold Q'_Plus. rewrite <-H6. pose proof H5. inQ' H7 a0 b0.
  assert (x ∈ [x]). { apply MKT41; eauto. }
  rewrite H6 in H12. clear H6. apply AxiomII in H12 as [].
  apply (H12 a b c d) in H; auto. rewrite <-H. apply MKT44; auto.
Qed.

(* 进一步验证 *Q上定义的加法对*Q封闭 *)
Property Q'_Plus_in_Q' : ∀ u v, u ∈ Q' -> v ∈ Q' -> (u + v) ∈ Q'.
Proof.
  intros. pose proof H. apply (Q'_Plus_Reasonable u v) in H1 as [x[]]; auto.
  assert (x ∈ [x]). { apply MKT41; eauto. }
  rewrite H2 in H3. clear H2. apply AxiomII in H3 as [].
  inQ' H a b. inQ' H0 c d. rewrite H7,H11. pose proof H.
  apply (H3 a b c d) in H12; auto. rewrite Q'_Plus_Instantiate; auto.
  rewrite <-H12; auto.
Qed.

Global Hint Resolve Q'_Plus_in_Q' : Q'.

(* 定义: *Q上的乘法, u * v 就是说   任意一个和u相等的等价类[(a,b)]
                              和 任意一个和v相等的等价类[(c,d)] 做运算,
                                 运算结果为等价类[(a*c),(b*d)].   *)
Definition Q'_Mult u v := ∩(\{ λ w, ∀ a b c d, a ∈ Z' -> b ∈ (Z' ~ [Z'0])
  -> c ∈ Z' -> d ∈ (Z' ~ [Z'0]) -> u = \[[a,b]\] -> v = \[[c,d]\]
  -> w = \[[(a · c)%z',(b · d)%z']\] \}).

Notation "u · v" := (Q'_Mult u v) : q'_scope.

(* 验证 *Q中定义的乘法运算的合理性: 对于任意*Q中的u和v, *Q上的乘法定义中的{}中只有
                               一个元素, 并且该唯一的元素也在*Q中, 于是u与v的
                               相乘结果形如 ∩[a] 是属于*Q且唯一的.       *)
Property Q'_Mult_Reasonable : ∀ u v, u ∈ Q' -> v ∈ Q'
  -> ∃ w, w ∈ Q' /\ [w] = \{ λ w, ∀ a b c d, a ∈ Z' -> b ∈ (Z' ~ [Z'0])
    -> c ∈ Z' -> d ∈ (Z' ~ [Z'0]) -> u = \[[a,b]\] -> v = \[[c,d]\]
    -> w = \[[(a · c)%z',(b · d)%z']\] \}.
Proof.
  intros. inQ' H a b. inQ' H0 c d. set (A := \[[(a · c)%z',(b · d)%z']\]).
  assert (A ∈ Q'). { apply Q'_Instantiate2; auto with Z'. }
  exists A. split; auto. apply AxiomI; split; intros.
  - apply MKT41 in H10; eauto. rewrite H10. apply AxiomII; split; eauto.
    intros. rewrite H4 in H15. rewrite H8 in H16.
    apply R_Z'_Property in H15,H16; auto. apply R_Z'_Property; auto with Z'.
    Z'split H12. Z'split H14. rewrite Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association c),<-(Z'_Mult_Association d),(Z'_Mult_Commutation c),
    (Z'_Mult_Commutation d),Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association a),<-(Z'_Mult_Association b); auto with Z'.
    rewrite H15,H16; auto.
  - apply AxiomII in H10 as []. apply MKT41; eauto.
Qed.

Property Q'_Mult_Instantiate : ∀ a b c d, a ∈ Z' -> b ∈ (Z' ~ [Z'0])
  -> c ∈ Z' -> d ∈ (Z' ~ [Z'0])
  -> \[[a,b]\] · \[[c,d]\] = \[[(a · c)%z',(b · d)%z']\].
Proof.
  intros. assert (\[[a,b]\] ∈ Q'). { apply Q'_Instantiate2; auto. }
  assert (\[[c,d]\] ∈ Q'). { apply Q'_Instantiate2; auto. } pose proof H3.
  apply (Q'_Mult_Reasonable (\[[a,b]\]) (\[[c,d]\])) in H5 as [w[]]; auto.
  unfold Q'_Mult. rewrite <-H6. destruct (@ MKT44 w); eauto.
  rewrite H7. assert (w ∈ [w]). { apply MKT41; eauto. }
  rewrite H6 in H9. apply AxiomII in H9 as []. apply H10; auto.
Qed.

(* 进一步验证 *Q上定义的乘法对*Q封闭 *)
Property Q'_Mult_in_Q' : ∀ u v, u ∈ Q' -> v ∈ Q' -> (u · v) ∈ Q'.
Proof.
  intros. pose proof H.
  apply (Q'_Mult_Reasonable u v) in H1 as [w[]]; auto.
  assert (w ∈ [w]). { apply MKT41; eauto. }
  rewrite H2 in H3. clear H2. apply AxiomII in H3 as []. inQ' H a b.
  inQ' H0 c d. rewrite H7,H11. pose proof H. apply (H3 a b c d) in H12; auto.
  rewrite Q'_Mult_Instantiate; auto. rewrite <-H12; auto.
Qed.

Global Hint Resolve Q'_Mult_in_Q' : Q'.

(* 验证 *Q中的关于零元的性质:
       u + Q'0 = u  ;  u * Q'0 = Q'0  ;  无零因子 *)
Property Q'_Plus_Property : ∀ u, u ∈ Q' -> u + Q'0 = u.
Proof.
  intros. inQ' H a b. rewrite H3,Q'0_Property,Q'_Plus_Instantiate; auto with Z'.
  apply R_Z'_Property; auto with Z'. rewrite Z'_Mult_Property2,Z'_Mult_Property2,
  Z'_Mult_Property1,Z'_Plus_Property,Z'_Mult_Commutation; auto with Z'.
Qed.

(* 验证 *Q中的加法满足交换律. *)
Property Q'_Plus_Commutation : ∀ u v, u ∈ Q' -> v ∈ Q' -> u + v = v + u.
Proof.
  intros. inQ' H a b. inQ' H0 c d.
  rewrite H4,H8,Q'_Plus_Instantiate,Q'_Plus_Instantiate; auto.
  rewrite (Z'_Mult_Commutation a),(Z'_Mult_Commutation b),
  (Z'_Mult_Commutation b),Z'_Plus_Commutation; auto with Z'.
Qed.

(* 验证 *Q中的加法满足结合律 *)
Property Q'_Plus_Association : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q'
  -> (u + v) + w = u + (v + w).
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. inQ' H1 m n.
  rewrite H5,H9,H13,Q'_Plus_Instantiate,Q'_Plus_Instantiate,
  Q'_Plus_Instantiate,Q'_Plus_Instantiate; auto with Z'.
  apply R_Z'_Property; auto with Z'. rewrite (Z'_Mult_Commutation _ n),
  (Z'_Mult_Distribution n),(Z'_Mult_Distribution b),(Z'_Mult_Commutation n),
  (Z'_Mult_Commutation n),(Z'_Plus_Association ((a · d) · n)),
  (Z'_Mult_Association a),(Z'_Mult_Association b),
  (Z'_Mult_Association b),(Z'_Mult_Association b),
  (Z'_Mult_Commutation (b · (d · n))); auto with Z'.
  Close Scope z'_scope.
Qed.

(* 验证 *Q中的加法满足消去律 *)
Property Q'_Plus_Cancellation : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q'
  -> u + v = u + w -> v = w.
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. inQ' H1 m n. rewrite H6,H10,H14 in *.
  rewrite Q'_Plus_Instantiate,Q'_Plus_Instantiate in H2; auto.
  apply R_Z'_Property in H2; auto with Z'. apply R_Z'_Property; auto.
  rewrite (Z'_Mult_Commutation _ (b · n)),
  Z'_Mult_Distribution,Z'_Mult_Distribution,
  (Z'_Mult_Commutation a),(Z'_Mult_Association b),
  <-(Z'_Mult_Association n),(Z'_Mult_Commutation n),
  (Z'_Mult_Association d),<-(Z'_Mult_Association b),
  (Z'_Mult_Commutation n) in H2; auto with Z'.
  apply Z'_Plus_Cancellation in H2; auto with Z'.
  rewrite Z'_Mult_Association,Z'_Mult_Association,
  <-(Z'_Mult_Association n),<-(Z'_Mult_Association d),
  (Z'_Mult_Commutation n),(Z'_Mult_Commutation d),
  Z'_Mult_Association,Z'_Mult_Association,
  <-(Z'_Mult_Association b b),<-(Z'_Mult_Association b b),
  (Z'_Mult_Commutation n) in H2; auto with Z'.
  apply Z'_Mult_Cancellation in H2; auto with Z'.
  assert ((b · b) ∈ (Z' ~ [Z'0])); auto with Z'. Z'split H15. auto.
  Close Scope z'_scope.
Qed.

(* *Q上定义的 Q'_Ord关系 满足加法保序 (需注意和 消去律 的区别).  *)
Property Q'_Plus_PrOrder : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q'
  -> u < v <-> (w + u) < (w + v).
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. inQ' H1 e f. Q'altH H5 a b b.
  Q'altH H9 c d d. Q'altH H13 e f f. rewrite H5,H9,H13.
  set (A := b · a). set (B := b · b).  set (C := d · c). set (D := d · d).
  set (M := f · e). set (N := f · f).
  assert (N ∈ (Z' ~ [Z'0]) /\ B ∈ (Z' ~ [Z'0]) /\ D ∈ (Z' ~ [Z'0]))
    as [Ha[Hb Hc]]. { repeat split; unfold N,B,D; auto with Z'. }
  split; intros; try rewrite Q'_Plus_Instantiate;
  try rewrite Q'_Plus_Instantiate;
  try rewrite Q'_Plus_Instantiate in H14;
  try rewrite Q'_Plus_Instantiate in H14;
  try apply Q'_Ord_Instantiate; unfold A,B,C,D,M,N; auto with Z'.
  - apply Q'_Ord_Instantiate in H14; unfold A,B,C,D; auto with Z'.
    replace (b · a) with A; replace (b · b) with B;
    replace (d · c) with C; replace (d · d) with D;
    replace (f · f) with N; replace (f · e) with M; auto.
    rewrite (Z'_Mult_Commutation _ (N · D)),
    Z'_Mult_Distribution,Z'_Mult_Distribution,
    Z'_Mult_Association,<-(Z'_Mult_Association D M B),
    (Z'_Mult_Commutation _ B),<-(Z'_Mult_Association N B),
    (Z'_Mult_Commutation D M); unfold A,B,C,D,M,N; auto with Z'.
    apply Z'_Plus_PrOrder; auto with Z'.
    replace (b · a) with A; replace (b · b) with B;
    replace (d · c) with C; replace (d · d) with D;
    replace (f · f) with N; replace (f · e) with M; auto.
    rewrite Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association D),<-(Z'_Mult_Association B),
    (Z'_Mult_Commutation D),(Z'_Mult_Commutation B),
    Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association N),<-(Z'_Mult_Association N),
    (Z'_Mult_Commutation D); unfold A,B,C,D,M,N; auto with Z'.
    apply Z'_Mult_PrOrder; auto with Z'.
  - apply Q'_Ord_Instantiate in H14; unfold A,B,C,D,M,N; auto with Z'.
    rewrite (Z'_Mult_Commutation _ (N · D)),
    Z'_Mult_Distribution,Z'_Mult_Distribution,Z'_Mult_Association,
    <-(Z'_Mult_Association D M B),(Z'_Mult_Commutation _ B),
    <-(Z'_Mult_Association N B),(Z'_Mult_Commutation D M) in H14;
    unfold A,B,C,D,M,N; auto with Z'.
    apply Z'_Plus_PrOrder in H14; unfold A,B,C,D,M,N; auto with Z'.
    rewrite Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association D),<-(Z'_Mult_Association B),
    (Z'_Mult_Commutation D),(Z'_Mult_Commutation B),
    Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association N),<-(Z'_Mult_Association N),
    (Z'_Mult_Commutation D) in H14;
    unfold A,B,C,D,M,N; auto with Z'.
    apply Z'_Mult_PrOrder in H14; unfold A,B,C,D,M,N; auto with Z'.
  Close Scope z'_scope.
Qed.

Corollary Q'_Plus_PrOrder_Corollary : ∀ u v, u ∈ Q' -> v ∈ Q'
  -> u < v <-> ∃! w, w ∈ Q' /\ Q'0 < w /\ u + w = v.
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. Q'altH H4 a b b. Q'altH H8 c d d.
  rewrite H4,H8. set (A := b · a). set (B := b · b). set (C := d · c).
  set (D := d · d). split; intros.
  - apply Q'_Ord_Instantiate in H9; unfold A,B,C,D; auto with Z'.
    apply Z'_Plus_PrOrder_Corollary in H9 as [w[[H9[]]]];
    unfold A,B,C,D; auto with Z'. exists (\[[w,(B · D)%z']\])%q'.
    assert (\[[w,(B · D)%z']\] ∈ Q')%q'.
    { apply Q'_Instantiate2; unfold A,B,C,D; auto with Z'. }
    assert (Q'0 < \[[w,(B · D)%z']\])%q'.
    { rewrite Q'0_Property; auto.
      apply Q'_Ord_Instantiate; unfold A,B,C,D; auto with Z'.
      rewrite Z'_Mult_Commutation,Z'_Mult_Property1,
      Z'_Mult_Commutation,Z'_Mult_Property2; auto with Z'. }
    assert (\[[A,B]\] + \[[w,(B · D)%z']\] = \[[C,D]\])%q'.
    { rewrite Q'_Plus_Instantiate,<-(Z'_Mult_Association A),
      (Z'_Mult_Commutation A B),Z'_Mult_Association,
      <-Z'_Mult_Distribution,H11,<-Z'_Mult_Association,
      <-Z'_Mult_Association; Q'alt C D (B · B); unfold A,B,C,D; auto with Z'. }
    repeat split; auto. intros x [H17[]].
    replace (b · a) with A in H18; replace (b · b) with B in H18;
    replace (d · c) with C in H18; replace (d · d) with D in H18; auto.
    rewrite <-H15 in H18. apply Q'_Plus_Cancellation in H18; auto.
    apply Q'_Instantiate2; unfold A,B; auto with Z'.
  - destruct H9 as [w[[H9[]]]].
    apply (Q'_Plus_PrOrder _ _ (\[[A,B]\])%q') in H10; auto.
    rewrite H11,Q'_Plus_Property in H10; auto.
    apply Q'_Instantiate2; unfold A,B; auto with Z'. apply Q'0_in_Q'; auto.
    apply Q'_Instantiate2; unfold A,B; auto with Z'.
  Close Scope z'_scope.
Qed.

(* 验证 *Q中负元的性质:
      对任意*Q中的元u, 存在唯一的负元v使得 u+v=0. *)
Property Q'_Neg : ∀ u, u ∈ Q' -> ∃! v, v ∈ Q' /\ u + v = Q'0.
Proof.
  intros. inQ' H a b. pose proof H. apply Z'_Neg in H4 as [a0[[]]]; auto.
  assert (\[[a0,b]\] ∈ Q'). { apply Q'_Instantiate2; auto. }
  assert (u + \[[a0,b]\] = Q'0).
  { rewrite H3,Q'0_Property,Q'_Plus_Instantiate,Z'_Mult_Commutation,
    <-Z'_Mult_Distribution,H5,Z'_Mult_Property1; auto.
    apply R_Z'_Property; auto with Z'.
    rewrite Z'_Mult_Property2,Z'_Mult_Property1; auto with Z'. }
  exists (\[[a0,b]\]). repeat split; auto. intros x []. inQ' H9 c d.
  rewrite H14. apply R_Z'_Property; auto.
  rewrite H3,H14,Q'_Plus_Instantiate in *; auto.
  rewrite <-H8 in H10. apply R_Z'_Property in H10; auto with Z'.
  rewrite (Z'_Mult_Commutation _ (b · b)%z'),Z'_Mult_Distribution,
  Z'_Mult_Distribution,(Z'_Mult_Association b b),<-(Z'_Mult_Association b a d),
  (Z'_Mult_Commutation b a),(Z'_Mult_Association a b d),
  <-(Z'_Mult_Association b a),(Z'_Mult_Commutation b a),
  (Z'_Mult_Commutation (a · b)%z') in H10; auto with Z'.
  apply Z'_Plus_Cancellation in H10; auto with Z'.
  rewrite (Z'_Mult_Association b d),
  <-(Z'_Mult_Association d b),(Z'_Mult_Commutation d b),
  (Z'_Mult_Association b d a0),<-(Z'_Mult_Association b),
  (Z'_Mult_Commutation d a0) in H10; auto with Z'.
  apply Z'_Mult_Cancellation in H10; auto with Z'. intro.
  apply Z'_Mult_Property3 in H15 as []; auto.
Qed.

(* 负元具体化:
      对任意*Z中的元a b(非零) 和 *Q中的元u, 若[a,b] + u = 0, 则u = [-a,b].  *)
Property Q'_Neg_Instantiate : ∀ a a0 b u, a ∈ Z' -> a0 ∈ Z'
  -> b ∈ (Z' ~ [Z'0]) -> u ∈ Q' -> (a + a0)%z' = Z'0
  -> \[[a,b]\] + u = Q'0 -> u = \[[a0,b]\].
Proof.
  Open Scope z'_scope.
  intros. inQ' H2 c d. rewrite H8 in *.
  rewrite Q'_Plus_Instantiate,Q'0_Property in H4; auto.
  Z'split H1. Z'split H5. apply R_Z'_Property in H4; auto; auto with Z'.
  apply R_Z'_Property; auto. rewrite Z'_Mult_Property2,Z'_Mult_Property1 in H4;
  auto with Z'. assert (d · (a + a0) = d · Z'0). { rewrite H3; auto. }
  rewrite Z'_Mult_Distribution,Z'_Mult_Property1,<-H4,
  (Z'_Mult_Commutation d a),(Z'_Mult_Commutation b c) in H13; auto.
  apply Z'_Plus_Cancellation in H13; auto with Z'.
  Close Scope z'_scope.
Qed.

Property Q'_Mult_Property1 : ∀ u, u ∈ Q' -> u · Q'0 = Q'0.
Proof.
  intros. inQ' H a b.
  rewrite H3,Q'0_Property,Q'_Mult_Instantiate; auto with Z'.
  apply R_Z'_Property; auto with Z'.
  rewrite Z'_Mult_Property1,Z'_Mult_Property2,Z'_Mult_Property2,
  Z'_Mult_Property1; auto with Z'.
Qed.

(* 验证 *Q中的关于幺元的性质:
       u * Q'1 = u *)
Property Q'_Mult_Property2 : ∀ u, u ∈ Q' -> u · Q'1 = u.
Proof.
  intros. inQ' H a b. rewrite H3,Q'1_Property,Q'_Mult_Instantiate; auto with Z'.
  apply R_Z'_Property; auto with Z'.
  rewrite Z'_Mult_Property2,Z'_Mult_Property2,Z'_Mult_Commutation; auto with Z'.
Qed.

(* 无零因子 *)
Property Q'_Mult_Property3 : ∀ u v, u ∈ Q' -> v ∈ Q' -> u · v = Q'0
  -> u = Q'0 \/ v = Q'0.
Proof.
  intros. inQ' H a b. inQ' H0 c d. rewrite H5,H9 in *.
  rewrite Q'_Mult_Instantiate,Q'0_Property in *; auto.
  apply R_Z'_Property in H1; auto with Z'.
  rewrite Z'_Mult_Property2,Z'_Mult_Property1 in H1; auto with Z'.
  apply Z'_Mult_Property3 in H1; auto.
  destruct H1; [left|right]; apply R_Z'_Property; auto with Z';
  rewrite Z'_Mult_Property2,Z'_Mult_Property1; auto.
Qed.

(* 验证 *Q中的乘法满足交换律. *)
Property Q'_Mult_Commutation : ∀ u v, u ∈ Q' -> v ∈ Q' -> u · v = v · u.
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. rewrite H4,H8.
  rewrite Q'_Mult_Instantiate,Q'_Mult_Instantiate; auto.
  apply R_Z'_Property; auto with Z'.
  rewrite (Z'_Mult_Commutation a),(Z'_Mult_Commutation d),
  (Z'_Mult_Commutation (c · a)); auto with Z'.
  Close Scope z'_scope.
Qed.

(* 验证 *Q中的乘法满足结合律. *)
Property Q'_Mult_Association : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q'
  -> (u · v) · w = u · (v · w).
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. inQ' H1 m n.
  rewrite H5,H9,H13. rewrite Q'_Mult_Instantiate,
  Q'_Mult_Instantiate,Q'_Mult_Instantiate,Q'_Mult_Instantiate; auto with Z'.
  apply R_Z'_Property; auto with Z'.
  rewrite (Z'_Mult_Association a),(Z'_Mult_Association b),
  (Z'_Mult_Commutation (a · (c · m))); auto with Z'.
  Close Scope z'_scope.
Qed.

(* 验证 *Q中的乘法满足分配律. *)
Property Q'_Mult_Distribution : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q'
  -> u · (v + w) = (u · v) + (u · w).
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. inQ' H1 m n. rewrite H5,H9,H13.
  rewrite Q'_Plus_Instantiate,Q'_Mult_Instantiate,Q'_Mult_Instantiate,
  Q'_Mult_Instantiate,Q'_Plus_Instantiate; auto with Z'.
  apply R_Z'_Property; auto with Z'; auto with Z'.
  rewrite (Z'_Mult_Association a c),
  (Z'_Mult_Association b d (a · m)%z'),
  <-(Z'_Mult_Association c),<-(Z'_Mult_Association d),
  (Z'_Mult_Commutation c b),(Z'_Mult_Commutation d a),
  (Z'_Mult_Association b c),(Z'_Mult_Association a d),
  <-(Z'_Mult_Association a b),<-(Z'_Mult_Association b a),
  (Z'_Mult_Commutation a b),<-Z'_Mult_Distribution,
  (Z'_Mult_Association b a),
  <-(Z'_Mult_Association (b · (d · n))%z' b _),
  <-(Z'_Mult_Association b d n),(Z'_Mult_Association _ n),
  (Z'_Mult_Commutation n b); try apply Z'_Mult_Commutation; auto with Z'.
  Close Scope z'_scope.
Qed.

(* 验证: 乘法消去律 *)
Property Q'_Mult_Cancellation : ∀ w u v, w ∈ Q' -> u ∈ Q' -> v ∈ Q' -> w <> Q'0
  -> w · u = w · v <-> u = v.
Proof.
  split; intros.
  - inQ' H a b. inQ' H0 c d. inQ' H1 m n.
    assert (a ∈ (Z' ~ [Z'0])).
    { pose proof Z'0_in_Z'. apply MKT4'; split; auto.
      apply AxiomII; split; eauto. intro. apply MKT41 in H17; eauto. elim H2.
      rewrite H7,H17,Q'0_Property; auto. apply R_Z'_Property; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Property1; auto. }
    Z'split H16. rewrite H7,H11,H15 in *.
    rewrite Q'_Mult_Instantiate,Q'_Mult_Instantiate in H3; auto.
    apply R_Z'_Property in H3; auto with Z'. apply R_Z'_Property; auto.
    rewrite Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association c),<-(Z'_Mult_Association d),
    (Z'_Mult_Commutation c),(Z'_Mult_Commutation d),
    Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association a),<-(Z'_Mult_Association b),
    (Z'_Mult_Commutation a) in H3; auto with Z'.
    apply Z'_Mult_Cancellation in H3; auto with Z'. intro.
    apply Z'_Mult_Property3 in H19 as []; auto.
  - rewrite H3; auto.
Qed.

(* *Q上定义的 Q'_Ord关系 满足乘法保序 (需注意和 消去律 的区别).  *)
Property Q'_Mult_PrOrder : ∀ u v w,  u ∈ Q' -> v ∈ Q' -> w ∈ Q' -> Q'0 < w
  -> u < v <-> (w · u) < (w · v).
Proof.
  Open Scope z'_scope.
  intros. inQ' H a b. inQ' H0 c d. inQ' H1 e f.
  Q'altH H6 a b b. Q'altH H10 c d d. Q'altH H14 e f f.
  rewrite H6,H10,H14. rewrite H14 in H2.
  set (A := b · a). set (B := b · b). set (C := d · c). set (D := d · d).
  set (M := f · e). set (N := f · f). rewrite Q'0_Property in H2; auto.
  apply Q'_Ord_Instantiate in H2; auto with Z'.
  rewrite Z'_Mult_Commutation,(Z'_Mult_Commutation Z'1),
  Z'_Mult_Property1,Z'_Mult_Property2 in H2; auto with Z'.
  split; intros.
  - apply Q'_Ord_Instantiate in H15; unfold A,B,C,D; auto with Z'.
    rewrite Q'_Mult_Instantiate,Q'_Mult_Instantiate;
    unfold A,B,C,D,M,N; auto with Z'. apply Q'_Ord_Instantiate; auto with Z'.
    replace (b · a) with A; replace (b · b) with B;
    replace (d · c) with C; replace (d · d) with D;
    replace (f · f) with N; replace (f · e) with M; auto.
    rewrite Z'_Mult_Association,Z'_Mult_Association,
    (Z'_Mult_Commutation A),(Z'_Mult_Commutation B),
    Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association M),<-(Z'_Mult_Association N),
    (Z'_Mult_Commutation D),(Z'_Mult_Commutation N),
    (Z'_Mult_Commutation C); unfold A,B,C,D,M,N; auto with Z'.
    apply Z'_Mult_PrOrder; auto with Z'.
  - apply Q'_Ord_Instantiate; unfold A,B,C,D; auto with Z'.
    rewrite Q'_Mult_Instantiate,Q'_Mult_Instantiate in H15;
    unfold A,B,C,D,M,N; auto with Z'.
    apply Q'_Ord_Instantiate in H15; unfold A,B,C,D,M,N; auto with Z'.
    rewrite Z'_Mult_Association,Z'_Mult_Association,
    (Z'_Mult_Commutation A),(Z'_Mult_Commutation B),
    Z'_Mult_Association,Z'_Mult_Association,
    <-(Z'_Mult_Association M),<-(Z'_Mult_Association N),
    (Z'_Mult_Commutation D),(Z'_Mult_Commutation N),
    (Z'_Mult_Commutation C) in H15; unfold A,B,C,D,M,N; auto with Z'.
    apply Z'_Mult_PrOrder in H15; unfold A,B,C,D,M,N; auto with Z'.
  Close Scope z'_scope.
Qed.

(* 验证 *Q中逆元的性质:
       对任意*Q中的非零元u, 存在唯一的逆元v使得 u*v=1.
       [注: 此性质是*Z所不具备的, 同时也是利用等价类构造*Q的目的.] *)
Property Q'_Inv : ∀ u, u ∈ Q' -> u <> Q'0
  -> ∃! u1, u1 ∈ Q' /\ u1 <> Q'0 /\ u · u1 = Q'1.
Proof.
  intros. inQ' H a b. assert (a <> Z'0).
  { intro. elim H0. rewrite H4,H5,Q'0_Property; auto.
    apply R_Z'_Property; auto with Z'.
    rewrite Z'_Mult_Property1,Z'_Mult_Property2; auto with Z'. }
  assert (a ∈ (Z' ~ [Z'0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H6; auto. pose proof Z'0_in_Z'; eauto. }
  assert (\[[b,a]\] ∈ Q'). { apply Q'_Instantiate2; auto. }
  assert (\[[b,a]\] <> Q'0).
  { intro. rewrite Q'0_Property in H8; auto.
    apply R_Z'_Property in H8; auto with Z'.
    rewrite Z'_Mult_Property1,Z'_Mult_Property2 in H8; auto. }
  assert (u · \[[b,a]\] = Q'1).
  { rewrite H4,Q'_Mult_Instantiate,Q'1_Property; auto.
    apply R_Z'_Property; auto; auto with Z'.
    rewrite Z'_Mult_Property2,Z'_Mult_Property2,
    Z'_Mult_Commutation; auto with Z'. }
  exists (\[[b,a]\]). repeat split; auto. intros x [H10[]]. inQ' H10 c d.
  rewrite H16. apply R_Z'_Property; auto. rewrite H16,<-H9,H4,
  Q'_Mult_Instantiate,Q'_Mult_Instantiate in H12; auto.
  apply R_Z'_Property in H12; auto with Z'.
  rewrite Z'_Mult_Commutation,(Z'_Mult_Commutation (b · d)%z'),
  (Z'_Mult_Commutation a b) in H12; auto with Z'.
  apply Z'_Mult_Cancellation in H12; auto with Z'. intro.
  apply Z'_Mult_Property3 in H17 as []; auto.
Qed.

(* 逆元具体化:
       对任意*Z中的元a b 和 *Q中的元u, 若[a,b] * u = 1, 则u = [b,a]. *)
Property Q'_Inv_Instantiate : ∀ a b u, a ∈ (Z' ~ [Z'0]) -> b ∈ (Z' ~ [Z'0])
  -> u ∈ Q' -> \[[a,b]\] · u = Q'1 -> u = \[[b,a]\].
Proof.
  intros. inQ' H1 c d. Z'split H. Z'split H0. rewrite H6 in *.
  rewrite Q'_Mult_Instantiate,Q'1_Property in H2; auto.
  apply R_Z'_Property in H2; auto with Z'.
  rewrite Z'_Mult_Property2,Z'_Mult_Property2 in H2; auto with Z'.
  apply R_Z'_Property; auto.
  rewrite Z'_Mult_Commutation,(Z'_Mult_Commutation d); auto.
Qed.

(* 定义: *Q中的减法. *)
Definition Q'_Minus v u := ∩(\{ λ w, w ∈ Q' /\ u + w = v \}).

Notation "u - v" := (Q'_Minus u v) : q'_scope.

(* 定义减法的合理性: 任何*Q中的u和v, 都存在唯一u0使得 u + u0 = v. *)
Property Q'_Minus_Reasonable : ∀ u v, u ∈ Q' -> v ∈ Q'
  -> ∃! w, w ∈ Q' /\ u + w = v.
Proof.
  intros. assert (u ∈ Q' /\ v ∈ Q') as []; auto.
  apply (Q'_Ord_Tri u v) in H1 as [H1|[]]; auto; clear H2.
  - apply Q'_Plus_PrOrder_Corollary in H1 as [x[[H1[]]]]; auto.
    exists x. repeat split; auto. intros x' []. rewrite <-H3 in H6.
    apply Q'_Plus_Cancellation in H6; auto.
  - apply Q'_Plus_PrOrder_Corollary in H1 as [x[[H1[]]]]; auto.
    pose proof H1. apply Q'_Neg in H5 as [x0[[]]]; auto.
    exists x0. repeat split; auto.
    rewrite <-H3,Q'_Plus_Association,H6,Q'_Plus_Property; auto.
    intros x' []. rewrite <-H3,Q'_Plus_Association in H9; auto.
    assert (v + (x + x') = v + Q'0). { rewrite Q'_Plus_Property; auto. }
    apply Q'_Plus_Cancellation in H10; auto.
    apply Q'_Plus_in_Q'; auto. apply Q'0_in_Q'; auto.
  - exists Q'0. pose proof Q'0_in_Q'. repeat split; auto.
    rewrite Q'_Plus_Property; auto. intros x []. rewrite H1 in H4.
    assert (v + x = v + Q'0). { rewrite Q'_Plus_Property; auto. }
    apply Q'_Plus_Cancellation in H5; auto.
Qed.

(* 减法性质: 减法与加法之间的关系. *)
Property Q'_Minus_Plus : ∀ u w v, u ∈ Q' -> w ∈ Q' -> v ∈ Q'
  -> u + w = v <-> v - u = w.
Proof.
  split; intros.
  - assert (\{ λ w, w ∈ Q' /\ u + w = v \} = [w]).
    { apply AxiomI; split; intros. apply AxiomII in H3 as [].
      apply (Q'_Minus_Reasonable u v) in H as [x[[]]]; auto. apply MKT41; eauto.
      assert (x = w). { apply H6; auto. } assert (x = z). { apply H6; auto. }
      rewrite <-H7,<-H8; auto. apply MKT41 in H3; eauto.
      rewrite H3. apply AxiomII; split; eauto. }
    unfold Q'_Minus. rewrite H3. destruct (@ MKT44 w); eauto.
  - assert (∃ a, Ensemble a /\ [a] = \{ λ x, x ∈ Q' /\ u + x = v \}).
    { pose proof H. apply (Q'_Minus_Reasonable u v) in H3 as [x[[]]]; auto.
      exists x. split; eauto. apply AxiomI; split; intros. apply MKT41 in H6;
      eauto. rewrite H6. apply AxiomII; split; eauto. apply AxiomII in H6 as [H6[]].
      apply MKT41; eauto. symmetry. apply H5; auto. }
    destruct H3 as [x[]]. unfold Q'_Minus in H2. rewrite <-H4 in H2.
    destruct (@ MKT44 x); auto. rewrite H5 in H2.
    assert (x ∈ [x]). { apply MKT41; auto. }
    rewrite H4 in H7. apply AxiomII in H7 as [H7[]]. rewrite <-H2; auto.
Qed.

(* 验证: *Q中定义的减法在*Q中封闭. *)
Property Q'_Minus_in_Q' : ∀ v u, v ∈ Q' -> u ∈ Q' -> (v - u) ∈ Q'.
Proof.
  intros. pose proof H. apply (Q'_Minus_Reasonable u) in H1 as [x[[]]]; auto.
  apply Q'_Minus_Plus in H2; auto. rewrite H2; auto.
Qed.

Global Hint Resolve Q'_Minus_in_Q' : Q'.

(* 定义: *Q中的除法.*)
Definition Q'_Divide v u := ∩(\{ λ w, w ∈ Q' /\ u <> Q'0 /\ u · w = v \}).

Notation "v / u" := (Q'_Divide v u) : q'_scope.

(* 除法合理性: 任何*Q中的非零u和任何v, 都存在唯一w使得 u · w = v. *)
Property Q'_Divide_Reasonable : ∀ u v, u ∈ Q' -> v ∈ Q' -> u <> Q'0
  -> ∃! w, w ∈ Q' /\ u · w = v.
Proof.
  intros. pose proof H. apply Q'_Inv in H2 as [w[[H2[]]]]; auto.
  exists (w · v). repeat split; auto with Q'.
  - rewrite <-Q'_Mult_Association,H4,Q'_Mult_Commutation,
    Q'_Mult_Property2; auto with Q'.
  - intros x []. rewrite <-H7,<-Q'_Mult_Association,(Q'_Mult_Commutation w),
    H4,Q'_Mult_Commutation,Q'_Mult_Property2; auto with Q'.
Qed.

(* 除法性质: 除法与加法之间的关系. *)
Property Q'_Divide_Mult : ∀ u w v, u ∈ Q' -> u <> Q'0 -> w ∈ Q' -> v ∈ Q'
  -> u · w = v <-> v / u = w.
Proof.
  split; intros.
  - assert (\{ λ x, x ∈ Q' /\ u <> Q'0 /\ u · x = v \} = [w]).
    { apply AxiomI; split; intros.
      - apply AxiomII in H4 as [_[H4[]]]. rewrite <-H3 in H6.
        apply MKT41; eauto. apply (Q'_Mult_Cancellation u); auto.
      - apply AxiomII; split; eauto. apply MKT41 in H4; eauto. subst; auto. }
    unfold Q'_Divide. rewrite H4. apply MKT44; eauto.
  - assert (∃ a, Ensemble a
      /\ [a] = \{ λ x, x ∈ Q' /\ u <> Q'0 /\ u · x = v \}) as [a[]].
    { pose proof H. apply (Q'_Divide_Reasonable u v) in H4 as [a[[]]]; auto.
      exists a. split; eauto. apply AxiomI; split; intros.
      - apply MKT41 in H7; eauto. rewrite H7. apply AxiomII; split; eauto.
      - apply AxiomII in H7 as [_[H7[]]]. apply MKT41; eauto.
        rewrite <-H5 in H9. apply Q'_Mult_Cancellation in H9; auto. }
    unfold Q'_Divide in H3. rewrite <-H5 in H3.
    assert (a ∈ [a]). { apply MKT41; auto. }
    rewrite H5 in H6. apply AxiomII in H6 as [_[H6[]]].
    apply MKT44 in H4 as [H4 _]. rewrite <-H3,H4; auto.
Qed.

(* 验证: *Q中定义的除法在*Q中封闭. *)
Property Q'_Divide_in_Q' : ∀ v u, v ∈ Q' -> u ∈ Q' -> u <> Q'0
  -> (v / u) ∈ Q'.
Proof.
  intros. pose proof H0. apply (Q'_Divide_Reasonable u v) in H2 as [w[[]]]; auto.
  apply Q'_Divide_Mult in H3; auto. rewrite H3; auto.
Qed.

Global Hint Resolve Q'_Divide_in_Q' : Q'.

Property Q'_Minus_Property1 : ∀ u, u ∈ Q' -> u - u = Q'0.
Proof.
  intros. apply Q'_Minus_Plus; auto with Q'.
  rewrite Q'_Plus_Property; auto.
Qed.

(* u - 0 = u *)
Property Q'_Minus_Property2 : ∀ u, u ∈ Q' -> u - Q'0 = u.
Proof.
  intros. apply Q'_Minus_Plus; auto with Q'.
  rewrite Q'_Plus_Commutation,Q'_Plus_Property; auto with Q'.
Qed.

Property Q'_Divide_Property1 : ∀ u, u ∈ Q' -> u <> Q'0 -> u / u = Q'1.
Proof.
  intros. apply Q'_Divide_Mult; auto with Q'.
  rewrite Q'_Mult_Property2; auto.
Qed.

Property Q'_Divide_Property2 : ∀ u, u ∈ Q' -> u / Q'1 = u.
Proof.
  intros. apply Q'_Divide_Mult; auto with Q'.
  intro. elim Q'0_isnot_Q'1; auto.
  rewrite Q'_Mult_Commutation,Q'_Mult_Property2; auto with Q'.
Qed.

Property Q'_Divide_Property3 : ∀ v u, v ∈ Q' -> u ∈ Q' -> u <> Q'0
  -> u · (v / u) = v.
Proof.
  intros. apply Q'_Divide_Mult; auto. apply Q'_Divide_in_Q'; auto.
Qed.

(* 验证: 加减法的混合运算结合律. *)
Property Q'_Mix_Association1 : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q'
  -> (u + v) - w = u + (v - w).
Proof.
  intros. assert ((u + v) ∈ Q'). { apply Q'_Plus_in_Q'; auto. }
  pose proof H1. apply (Q'_Minus_Reasonable w (u + v)) in H3 as [x[[]]]; auto.
  pose proof H1. apply (Q'_Minus_Reasonable w v) in H6 as [y[[]]]; auto.
  apply Q'_Minus_Plus in H4; auto. rewrite H4,<-H7.
  assert ((w + y) - w = y).
  { apply Q'_Minus_Plus; auto. apply Q'_Plus_in_Q'; auto. }
  rewrite H9. rewrite <-H7 in H4.
  apply Q'_Minus_Plus in H4; try apply Q'_Plus_in_Q'; auto.
  rewrite <-Q'_Plus_Association,(Q'_Plus_Commutation u w),
  Q'_Plus_Association in H4; auto. apply Q'_Plus_Cancellation in H4;
  try apply Q'_Plus_in_Q'; auto. apply Q'_Plus_in_Q'; auto.
Qed.

Property Q'_Mix_Association2 : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q' -> w <> Q'0
  -> u · (v / w) = (u · v) / w.
Proof.
  intros. apply (Q'_Mult_Cancellation w); auto.
  apply Q'_Mult_in_Q',Q'_Divide_in_Q'; auto.
  apply Q'_Divide_in_Q'; auto. apply Q'_Mult_in_Q'; auto.
  rewrite Q'_Divide_Property3; auto with Q'.
  rewrite <-Q'_Mult_Association,(Q'_Mult_Commutation w),
  Q'_Mult_Association,Q'_Divide_Property3; auto;
  apply Q'_Divide_in_Q'; auto.
Qed.

(* 乘法对减法的分配律 *)
Property Q'_Mult_Distribution_Minus : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q'
  -> u · (v - w) = (u · v) - (u · w).
Proof.
  intros. pose proof H0.
  apply (Q'_Minus_Reasonable w v) in H2 as [x[[]]]; auto.
  pose proof H3. apply Q'_Minus_Plus in H5; auto.
  rewrite H5,<-H3. rewrite Q'_Mult_Distribution,
  Q'_Plus_Commutation,Q'_Mix_Association1; try apply Q'_Mult_in_Q'; auto.
  assert ((u · w) - (u · w) = Q'0).
  { apply Q'_Minus_Plus; try apply Q'_Mult_in_Q'; auto.
    apply Q'0_in_Q'; auto. rewrite Q'_Plus_Property;
    try apply Q'_Mult_in_Q'; auto. }
  rewrite H6,Q'_Plus_Property; try apply Q'_Mult_in_Q'; auto.
Qed.

(* *Q除法性质补充 *)
Property Q'_Divide_Distribution : ∀ u v w, u ∈ Q' -> v ∈ Q' -> w ∈ Q'
  -> w <> Q'0 -> (u + v) / w = (u / w) + (v / w).
Proof.
  intros. apply (Q'_Mult_Cancellation w); auto with Q'.
  rewrite Q'_Divide_Property3,Q'_Mult_Distribution,
  Q'_Divide_Property3,Q'_Divide_Property3; auto with Q'.
Qed.

(* *Q中的分数平方 *)
Property Q'_Frac_Square : ∀ u v, u ∈ Q' -> v ∈ Q' -> v <> Q'0
  -> (u · u) / (v · v) = (u / v) · (u / v).
Proof.
  intros. assert ((v · v) <> Q'0).
  { intro. apply Q'_Mult_Property3 in H2 as []; auto. }
  apply (Q'_Mult_Cancellation v); auto with Q'.
  rewrite <-Q'_Mult_Association,Q'_Divide_Property3; auto with Q'.
  apply (Q'_Mult_Cancellation v); auto with Q'.
  rewrite <-Q'_Mult_Association,Q'_Divide_Property3; auto with Q'.
  rewrite <-Q'_Mult_Association,(Q'_Mult_Commutation v),
  Q'_Mult_Association,Q'_Divide_Property3; auto with Q'.
Qed.

(* 定义: *Q中的绝对值函数, 用于表示*Q中元素的绝对值. *)
Definition Q'_Abs := \{\ λ u v, u ∈ Q'
  /\ ((u < Q'0 /\ v = Q'0 - u) \/ (u = Q'0 /\ v = Q'0) \/ (Q'0 < u /\ v = u)) \}\.

Notation "| u | " := ((Q'_Abs)[u])(u at level 0, at level 5) : q'_scope.

Property Q'Abs_is_Function : Function Q'_Abs /\ dom(Q'_Abs) = Q'
  /\ ran(Q'_Abs) ⊂ Q'.
Proof.
  assert (Function Q'_Abs).
  { split.
    - unfold Relation; intros.
      apply AxiomII in H as [H[x[y[]]]]; eauto.
    - intros. apply AxiomII' in H as [H[]].
      apply AxiomII' in H0 as [H0[]]. destruct H2,H4.
      + destruct H2,H4. rewrite H5,H6; auto.
      + destruct H2,H4; destruct H4. rewrite <-H4 in H2.
        elim (Q'_Ord_irReflex x x); auto.
        apply (Q'_Ord_Trans x _ x) in H2; auto.
        elim (Q'_Ord_irReflex x x); auto. apply Q'0_in_Q'; auto.
      + destruct H2; destruct H2; destruct H4. rewrite <-H2 in H4.
        elim (Q'_Ord_irReflex x x); auto.
        apply (Q'_Ord_Trans x _ x) in H4; auto.
        elim (Q'_Ord_irReflex x x); auto. apply Q'0_in_Q'; auto.
      + destruct H2,H4; destruct H2,H4; rewrite H5,H6; auto. }
  split; auto. split.
  - apply AxiomI; split; intros.
    + apply AxiomII in H0 as [H0[y]]. apply AxiomII' in H1; tauto.
    + apply AxiomII; split; eauto. pose proof Q'0_in_Q'.
      assert (z ∈ Q' /\ Q'0 ∈ Q') as []; auto.
      apply (Q'_Ord_Tri z Q'0) in H2 as [H2|[]]; auto; clear H3.
      * exists (Q'_Minus Q'0 z). apply AxiomII'; repeat split; auto.
        apply (Q'_Minus_in_Q' _ z) in H1; auto. apply MKT49a; eauto.
      * exists z. apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
      * exists z. apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
  - unfold Included; intros. apply AxiomII in H0 as [H0[]]. pose proof Q'0_in_Q'.
    apply AxiomII' in H1 as [H1[H3[H4|[]]]]; destruct H4.
    + rewrite H5. apply Q'_Minus_in_Q'; auto.
    + rewrite H5; auto.
    + rewrite H5; auto.
Qed.

Property Q'Abs_in_Q' : ∀ u, u ∈ Q' -> |u| ∈ Q'.
Proof.
  intros. destruct Q'Abs_is_Function as [H0[]]. rewrite <-H1 in H.
  apply Property_Value,Property_ran in H; auto.
Qed.

Global Hint Resolve Q'Abs_in_Q' : Q'.

(*--------------------以下为关于绝对值的常见性质----------------------*)
Property mt_Q'0_Q'Abs : ∀ u, u ∈ Q' -> Q'0 < u -> |u| = u.
Proof.
  intros. destruct Q'Abs_is_Function as [H1[]]. rewrite <-H2 in H.
  apply Property_Value in H; auto. pose proof Q'0_in_Q'.
  apply AxiomII' in H as [H[H5[H6|[]]]]; destruct H6; auto.
  - apply (Q'_Ord_Trans u _ u) in H6; auto.
    elim (Q'_Ord_irReflex u u); auto.
  - rewrite <-H6 in H0. elim (Q'_Ord_irReflex u u); auto.
Qed.

Property eq_Q'0_Q'Abs : ∀ u, u ∈ Q' -> |u| = Q'0 <-> u = Q'0.
Proof.
  intros. pose proof Q'0_in_Q'. destruct Q'Abs_is_Function as [H1[]].
  rewrite <-H2 in H. apply Property_Value,AxiomII' in H as [H[]]; auto.
  split; intros; destruct H5 as [H5|[]]; destruct H5; auto.
  - rewrite H7 in H6. apply Q'_Minus_Plus in H6; auto.
    rewrite Q'_Plus_Property in H6; auto.
  - rewrite H7 in H6; auto.
  - rewrite H7. apply Q'_Minus_Plus; auto. rewrite Q'_Plus_Property; auto.
  - rewrite <-H6; auto.
Qed.

Property lt_Q'0_Q'Abs : ∀ u, u ∈ Q' -> u < Q'0 -> |u| = Q'0 - u.
Proof.
  intros. pose proof Q'0_in_Q'. destruct Q'Abs_is_Function as [H2[]].
  rewrite <-H3 in H. apply Property_Value,AxiomII' in H as [H[]]; auto.
  destruct H6 as [H6|[]]; destruct H6; auto.
  - rewrite <-H6 in H0. elim (Q'_Ord_irReflex u u); auto.
  - apply (Q'_Ord_Trans u _ u) in H0; auto. elim (Q'_Ord_irReflex u u); auto.
Qed.

Property Q'0_le_Q'Abs : ∀ u, u ∈ Q' -> |u| ∈ Q' /\ (|u| = Q'0 \/ Q'0 < |u|).
Proof.
  intros. destruct Q'Abs_is_Function as [H0[]].
  assert (|u| ∈ Q').
  { rewrite <-H1 in H. apply Property_Value,Property_ran,H2 in H; auto. }
  split; auto. pose proof Q'0_in_Q'.
  assert (Q'0 ∈ Q' /\ u ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ u) in H5 as [H5|[]]; auto; clear H6.
  - right. pose proof H5. apply mt_Q'0_Q'Abs in H5; auto. rewrite H5. apply H6.
  - pose proof H5. apply lt_Q'0_Q'Abs in H6; auto.
    apply Q'_Plus_PrOrder_Corollary in H5 as [u0[[H5[]]]]; auto.
    right. rewrite H6. apply Q'_Minus_Plus in H8; auto. rewrite H8. apply H7.
  - left. symmetry in H5. apply eq_Q'0_Q'Abs in H5; auto.
Qed.

Property Self_le_Q'Abs : ∀ u, u ∈ Q' -> u = |u| \/ u < |u|.
Proof.
  intros. pose proof H. apply Q'0_le_Q'Abs in H0 as []; auto.
  pose proof Q'0_in_Q'. assert (Q'0 ∈ Q' /\ u ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ u) in H3 as [H3|[]]; auto; clear H4.
  - apply mt_Q'0_Q'Abs in H3; auto.
  - destruct H1. apply (eq_Q'0_Q'Abs u) in H1; auto.
    rewrite <-H1 in H3. elim (Q'_Ord_irReflex u u); auto.
    apply (Q'_Ord_Trans u) in H1; auto.
  - pose proof H3. symmetry in H3. apply eq_Q'0_Q'Abs in H3; auto.
    rewrite H4 in H3; auto.
Qed.

(* 绝对值对乘法保持 |ab| = |a|*|b| *)
Property Q'Abs_PrMult : ∀ u v, u ∈ Q' -> v ∈ Q' -> |(u · v)| = |u| · |v|.
Proof.
  intros. pose proof Q'0_in_Q'. pose proof Q'1_in_Q'.
  assert (Q'0 ∈ Q' /\ u ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ u) in H3; auto; clear H4.
  assert (Q'0 ∈ Q' /\ v ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ v) in H4; auto; clear H5.
  destruct H3 as [H3|[]].
  - destruct H4 as [H4|[]].
    + pose proof H4. apply (Q'_Mult_PrOrder _ _ u) in H5; auto.
      rewrite Q'_Mult_Property1 in H5; auto.
      apply mt_Q'0_Q'Abs in H5; try apply Q'_Mult_in_Q'; auto.
      apply mt_Q'0_Q'Abs in H3; apply mt_Q'0_Q'Abs in H4; auto.
      rewrite H3,H4,H5; auto.
    + pose proof H4. apply (Q'_Mult_PrOrder _ _ u) in H5; auto.
      rewrite Q'_Mult_Property1 in H5; auto.
      apply lt_Q'0_Q'Abs in H5; try apply Q'_Mult_in_Q'; auto.
      pose proof H4. apply lt_Q'0_Q'Abs in H6; auto.
      apply mt_Q'0_Q'Abs in H3; auto. rewrite H3,H5,H6.
      rewrite Q'_Mult_Distribution_Minus,Q'_Mult_Property1; auto.
    + rewrite <-H4,Q'_Mult_Property1; auto. symmetry in H4.
      pose proof H4. apply eq_Q'0_Q'Abs in H4; auto.
      rewrite <-H5,H4,Q'_Mult_Property1; auto. apply Q'Abs_in_Q'; auto.
  - destruct H4 as [H4|[]].
    + pose proof H3. apply (Q'_Mult_PrOrder _ _ v) in H5; auto.
      rewrite Q'_Mult_Property1 in H5; auto.
      apply lt_Q'0_Q'Abs in H5; try apply Q'_Mult_in_Q'; auto.
      pose proof H3. apply lt_Q'0_Q'Abs in H6; auto.
      apply mt_Q'0_Q'Abs in H4; auto.
      rewrite Q'_Mult_Commutation,H4,H5,H6; auto.
      rewrite (Q'_Mult_Commutation _ v),
      Q'_Mult_Distribution_Minus,Q'_Mult_Property1; auto.
      rewrite <-H6. apply Q'Abs_in_Q'; auto.
    + assert (Q'0 < (u · v)).
      { pose proof H4.
        apply Q'_Plus_PrOrder_Corollary in H5 as [v0[[H5[]]]]; auto.
        apply (Q'_Mult_PrOrder _ _ v0) in H3; auto.
        rewrite Q'_Mult_Property1 in H3; auto. pose proof H7.
        apply Q'_Minus_Plus in H9; auto.
        rewrite <-H9,Q'_Mult_Commutation,
        Q'_Mult_Distribution_Minus,Q'_Mult_Property1 in H3;
        try apply Q'_Minus_in_Q'; auto.
        apply (Q'_Plus_PrOrder _ _ (u · v)) in H3;
        try apply Q'_Mult_in_Q'; auto.
        rewrite Q'_Plus_Property,<-Q'_Mix_Association1,
        Q'_Plus_Property in H3; try apply Q'_Mult_in_Q'; auto.
        assert ((u · v) - (u · v) = Q'0).
        { apply Q'_Minus_Plus; try apply Q'_Mult_in_Q'; auto.
          rewrite Q'_Plus_Property; try apply Q'_Mult_in_Q'; auto. }
        rewrite H10 in H3; auto. apply Q'_Minus_in_Q';
        try apply Q'_Mult_in_Q'; auto. }
      apply lt_Q'0_Q'Abs in H3; apply lt_Q'0_Q'Abs in H4; auto.
      apply mt_Q'0_Q'Abs in H5; try apply Q'_Mult_in_Q'; auto.
      rewrite H3,H4,H5,Q'_Mult_Distribution_Minus,
      Q'_Mult_Property1,(Q'_Mult_Commutation (Q'0 - u)),
      Q'_Mult_Distribution_Minus,Q'_Mult_Property1,
      Q'_Mult_Commutation; try apply Q'_Minus_in_Q'; auto.
      symmetry. apply Q'_Minus_Plus; try apply Q'_Minus_in_Q';
      try apply Q'_Mult_in_Q'; auto.
      rewrite Q'_Plus_Commutation,<-Q'_Mix_Association1,
      Q'_Plus_Property; try apply Q'_Mult_in_Q'; auto.
      apply Q'_Minus_Plus; try apply Q'_Mult_in_Q'; auto.
      rewrite Q'_Plus_Property; try apply Q'_Mult_in_Q'; auto.
      apply Q'_Minus_in_Q'; try apply Q'_Mult_in_Q'; auto.
    + rewrite <-H4,Q'_Mult_Property1; auto. symmetry in H4.
      pose proof H4. apply eq_Q'0_Q'Abs in H4; auto.
      rewrite <-H5,H4,Q'_Mult_Property1; auto. apply Q'Abs_in_Q'; auto.
  - clear H4. rewrite <-H3,Q'_Mult_Commutation,Q'_Mult_Property1; auto.
    symmetry in H3. pose proof H3. apply eq_Q'0_Q'Abs in H3; auto.
    rewrite <-H4,H3,Q'_Mult_Commutation,Q'_Mult_Property1; auto;
    apply Q'Abs_in_Q'; auto.
Qed.

(* 绝对值不等式 |a+b| <= |a|+|b| *)
Property Q'Abs_inEqu : ∀ u v, u ∈ Q' -> v ∈ Q'
  -> |(u + v)| = |u| + |v| \/ |(u + v)| < (|u| + |v|).
Proof.
  intros. pose proof Q'0_in_Q'.
  pose proof H. apply (Q'_Plus_in_Q' u v) in H2; auto.
  assert (u ∈ Q' /\ Q'0 ∈ Q') as []; auto.
  apply (Q'_Ord_Tri u Q'0) in H3; auto; clear H4.
  assert (v ∈ Q' /\ Q'0 ∈ Q') as []; auto.
  apply (Q'_Ord_Tri v Q'0) in H4; auto; clear H5.
  assert ((u + v) ∈ Q' /\ Q'0 ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ Q'0) in H5; auto; clear H6.
  destruct H5 as [H5|[]].
  - assert (∀ a b, a ∈ Q' -> b ∈ Q' -> (a + b) < Q'0 -> a < Q'0 -> Q'0 < b
      -> |(a + b)| < (|a| + |b|)).
    { intros. pose proof H8.
      apply lt_Q'0_Q'Abs in H11; try apply Q'_Plus_in_Q'; auto.
      pose proof H9. apply lt_Q'0_Q'Abs in H12; auto.
      pose proof H10. apply mt_Q'0_Q'Abs in H13; auto.
      rewrite H11,H12,H13.
      apply (Q'_Plus_PrOrder _ _ (a + b));
      try apply Q'_Plus_in_Q'; try apply Q'_Minus_in_Q'; auto.
      apply Q'_Plus_in_Q'; auto.
      rewrite <-Q'_Mix_Association1,Q'_Plus_Property,
      <-Q'_Plus_Association,<-Q'_Mix_Association1,
      Q'_Plus_Property,(Q'_Plus_Commutation a b),
      (Q'_Mix_Association1 b a a); try apply Q'_Plus_in_Q';
      try apply Q'_Minus_in_Q'; auto.
      assert (a - a = Q'0 /\ (b + a) - (b + a) = Q'0) as [].
      { split; rewrite Q'_Minus_Property1; auto with Q'. }
      rewrite H14,H15. rewrite Q'_Plus_Property; auto.
      pose proof H10. apply (Q'_Plus_PrOrder _ _ b) in H16; auto.
      rewrite Q'_Plus_Property in H16; auto.
      apply (Q'_Ord_Trans _ b _); auto. apply Q'_Plus_in_Q'; auto. }
    pose proof H5 as H5'. apply lt_Q'0_Q'Abs in H5; auto.
    destruct H3 as [H3|[]].
    + pose proof H3 as H3'. apply lt_Q'0_Q'Abs in H3; auto.
      destruct H4 as [H4|[]].
      * apply lt_Q'0_Q'Abs in H4; auto. rewrite H3,H4,H5.
        left. apply Q'_Minus_Plus; auto.
        apply Q'_Plus_in_Q'; try apply Q'_Minus_in_Q'; auto.
        rewrite <-Q'_Plus_Association,
        <-(Q'_Mix_Association1 _ _ u),Q'_Plus_Property,
        (Q'_Plus_Commutation u v),Q'_Mix_Association1,
        <-Q'_Mix_Association1,Q'_Plus_Property,
        Q'_Plus_Commutation,Q'_Mix_Association1; auto;
        try apply Q'_Plus_in_Q'; try apply Q'_Minus_in_Q'; auto.
        assert (u - u = Q'0 /\ v - v = Q'0) as [].
        { split; rewrite Q'_Minus_Property1; auto with Q'. }
        rewrite H7,H8,Q'_Plus_Property; auto.
      * right. apply H6; auto.
      * left. pose proof H4. apply eq_Q'0_Q'Abs in H7; auto.
        rewrite H7,H4,Q'_Plus_Property,Q'_Plus_Property; auto.
        apply Q'Abs_in_Q'; auto.
    + pose proof H3. apply mt_Q'0_Q'Abs in H7; auto. destruct H4 as [H4|[]].
      * right. rewrite Q'_Plus_Commutation,(Q'_Plus_Commutation (|u|));
        try apply Q'Abs_in_Q'; auto. apply H6; auto.
        rewrite Q'_Plus_Commutation; auto.
      * apply (Q'_Plus_PrOrder _ _ u) in H4; auto.
        rewrite Q'_Plus_Property in H4; auto.
        apply (Q'_Ord_Trans Q'0),(Q'_Ord_Trans _ _ Q'0) in H4; auto.
        elim (Q'_Ord_irReflex Q'0 Q'0); auto.
      * apply (Q'_Plus_PrOrder _ _ v) in H3; auto.
        rewrite H4,Q'_Plus_Property,Q'_Plus_Commutation,
        Q'_Plus_Property in H3; auto.
        rewrite H4,Q'_Plus_Property in H5'; auto.
        apply (Q'_Ord_Trans _ _ u) in H5'; auto.
        elim (Q'_Ord_irReflex u u); auto.
    + left. pose proof H3. apply eq_Q'0_Q'Abs in H7; auto.
      rewrite H7,H3,Q'_Plus_Commutation,Q'_Plus_Property,
      Q'_Plus_Commutation,Q'_Plus_Property; auto;
      apply Q'Abs_in_Q'; auto.
  - pose proof H2. apply mt_Q'0_Q'Abs in H6; auto.
    rewrite H6. destruct H3 as [H3|[]].
    + pose proof H3. apply lt_Q'0_Q'Abs in H7; auto.
      pose proof H3. apply Q'_Plus_PrOrder_Corollary in H8 as
      [u0[[H8[]]_]]; auto. apply Q'_Minus_Plus in H10; auto.
      destruct H4 as [H4|[]].
      * apply (Q'_Plus_PrOrder _ _ u) in H4; auto.
        rewrite Q'_Plus_Property in H4; auto.
        apply (Q'_Ord_Trans _ _ Q'0),(Q'_Ord_Trans Q'0) in H4; auto.
        elim (Q'_Ord_irReflex Q'0 Q'0); auto.
      * right. apply mt_Q'0_Q'Abs in H4; auto.
        rewrite H4,H7,H10,Q'_Plus_Commutation,
        (Q'_Plus_Commutation _ v); auto. apply Q'_Plus_PrOrder; auto.
        apply (Q'_Ord_Trans _ Q'0); auto.
      * right. pose proof H4. apply eq_Q'0_Q'Abs in H11; auto.
        rewrite H11,H4,Q'_Plus_Property,Q'_Plus_Property; auto.
        rewrite H7,H10. apply (Q'_Ord_Trans _ Q'0); auto.
        apply Q'Abs_in_Q'; auto.
    + pose proof H3. apply mt_Q'0_Q'Abs in H7; auto.
      rewrite H7. destruct H4 as [H4|[]].
      * pose proof H4. apply lt_Q'0_Q'Abs in H8; auto.
        pose proof H4. apply Q'_Plus_PrOrder_Corollary in H4
        as [v0[[H4[]]_]]; auto. right.
        apply Q'_Minus_Plus in H11; auto. rewrite H8,H11.
        apply Q'_Plus_PrOrder; auto. apply (Q'_Ord_Trans _ Q'0); auto.
      * apply mt_Q'0_Q'Abs in H4; auto. left. rewrite H4; auto.
      * pose proof H4. apply eq_Q'0_Q'Abs in H8; auto.
        left. rewrite H8,H4; auto.
    + left. pose proof H3. apply eq_Q'0_Q'Abs in H7; auto.
      rewrite <-H6,H7,H3,Q'_Plus_Commutation,Q'_Plus_Property,
      Q'_Plus_Commutation,Q'_Plus_Property; try apply Q'Abs_in_Q'; auto.
  - pose proof H5. apply eq_Q'0_Q'Abs in H6; auto. rewrite H6.
    pose proof H; pose proof H0.
    apply Q'0_le_Q'Abs in H7 as []; apply Q'0_le_Q'Abs in H8 as []; auto.
    destruct H9,H10.
    + left. rewrite H9,H10. rewrite Q'_Plus_Property; auto.
    + right. rewrite H9,Q'_Plus_Commutation,Q'_Plus_Property; auto.
    + right. rewrite H10,Q'_Plus_Property; auto.
    + right. apply (Q'_Plus_PrOrder _ _ (|u|)) in H10; auto.
      rewrite Q'_Plus_Property in H10; auto.
      apply (Q'_Ord_Trans Q'0) in H10; auto. apply Q'_Plus_in_Q'; auto.
Qed.

(* 互为负元的数, 其绝对值相等. *)
Property Neg_Q'Abs_Equ : ∀ u v, u ∈ Q' -> v ∈ Q' -> u + v = Q'0
  -> |u| = |v|.
Proof.
  intros. pose proof Q'0_in_Q'.
  assert (Q'0 ∈ Q' /\ u ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ u) in H3; auto; clear H4.
  assert (Q'0 ∈ Q' /\ v ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ v) in H4; auto; clear H5.
  assert (∀ a b, a ∈ Q' -> b ∈ Q' -> a + b = Q'0 -> Q'0 < a
    -> b < Q'0 -> |a| = |b|) as Ha.
  { intros. pose proof H8. apply mt_Q'0_Q'Abs in H8; auto.
    pose proof H9. apply lt_Q'0_Q'Abs in H9; auto.
    apply Q'_Plus_PrOrder_Corollary in H11 as [b0[[H11[]]]]; auto.
    assert (b0 = a).
    { apply H14; repeat split; auto. rewrite Q'_Plus_Commutation; auto. }
    clear H14. apply Q'_Minus_Plus in H13; auto.
    rewrite H8,<-H15,<-H13,H9; auto. }
  destruct H3 as [H3|[]].
  - pose proof H3. apply mt_Q'0_Q'Abs in H5; auto.
    rewrite H5. destruct H4 as [H4|[]].
    + apply (Q'_Plus_PrOrder _ _ u) in H4; auto.
      rewrite H1,Q'_Plus_Property in H4; auto.
      apply (Q'_Ord_Trans _ _ u) in H4; auto.
      elim (Q'_Ord_irReflex u u); auto.
    + rewrite <-H5. apply Ha; auto.
    + rewrite <-H4,Q'_Plus_Property in H1; auto.
      rewrite <-H1 in H3. elim (Q'_Ord_irReflex u u); auto.
  - pose proof H3. apply lt_Q'0_Q'Abs in H5; auto.
    rewrite H5. destruct H4 as [H4|[]].
    + rewrite <-H5. symmetry. apply Ha; auto.
      rewrite Q'_Plus_Commutation; auto.
    + apply (Q'_Plus_PrOrder _  _ u) in H4; auto.
      rewrite Q'_Plus_Property in H4; auto.
      apply (Q'_Ord_Trans _ _ Q'0) in H4; auto.
      rewrite H1 in H4. elim (Q'_Ord_irReflex Q'0 Q'0); auto.
      apply Q'_Plus_in_Q'; auto.
    + rewrite <-H4,Q'_Plus_Property in H1; auto.
      rewrite <-H1 in H3. elim (Q'_Ord_irReflex u u); auto.
  - rewrite <-H3,Q'_Plus_Commutation,Q'_Plus_Property in H1; auto.
    rewrite <-H3,H1; auto.
Qed.
(*-----------------------------------------------------------------*)

(*定义一个新的类: 该类的形象为:

     { ...  [-Z'2,Z'1]  [-Z'1,Z'1]  [Z'0,Z'1]  [Z'1,Z'1]  [Z'2,Z'1]  ... }

     相对应到整数上即有:

     { ...      -2          -1          0          1          2      ... }

     [注: ① Z'n 表示*Z中与自然数n相对应的那个元素.
           ② 这种排序方式来源于*Q中序的定义.
           ③ '数的延伸'依旧隐含其中.              ]             *)
Definition Q'_Z' := \{ λ u, ∃ m, m ∈ Z' /\ u = \[[m,Z'1]\] \}.

(* *Q_*Z 是一个集 *)
Property Q'_Z'_is_Set : Ensemble Q'_Z'.
Proof.
  apply (MKT33 Q'). apply Q'_is_Set. unfold Included; intros.
  apply AxiomII in H as [H[x[]]]. apply AxiomII; split; auto.
  exists [x,Z'1]. split; auto. apply AxiomII'. repeat split; auto with Z'.
  apply MKT49a; eauto. pose proof Z'1_in_Z'. eauto.
Qed.

(* *Q_*Z 是*Q的真子集. *)
Property Q'_Z'_propersubset_Q' : Q'_Z' ⊂ Q' /\ Q'_Z' <> Q'.
Proof.
  Open Scope z'_scope.
  intros. assert (Q'_Z' ⊂ Q').
  { unfold Included; intros. apply AxiomII in H as [H[a[]]].
    rewrite H1. apply Q'_Instantiate2; auto with Z'. }
  assert ((F 0) ∈ N' /\ (F 1) ∈ N' /\ (F 2) ∈ N').
  { pose proof in_ω_0. pose proof in_ω_1. pose proof in_ω_2.
    apply Fn_in_N' in H1,H0. apply Fn_in_N' in H2. auto. }
  destruct H0 as [Ha[Hb Hc]]. split; auto. intro.
  assert (\[[F 2,F 0]\] ∈ (Z' ~ [Z'0])).
  { assert (\[[F 2,F 0]\] ∈ Z'). { apply Z'_Instantiate2; auto. }
    apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H2. rewrite Z'0_Property in H2.
    apply R_N'_Property in H2; auto. rewrite N'_Plus_Property,
    N'_Plus_Property in H2; auto. pose proof in_ω_0; pose proof in_ω_2.
    assert (0 <> 2).
    { intro. assert (0 ∈ 2). apply AxiomII; split; eauto.
      rewrite <-H5 in H6. elim (@ MKT16 0); auto. }
    apply (Example2 ω) in H5; auto. pose proof Z'0_in_Z'; eauto. }
  assert (\[[Z'1,(\[[F 2,F 0]\])%z']\] ∈ Q')%q'.
  { apply Q'_Instantiate2; auto with Z'. }
  rewrite <-H0 in H2. apply AxiomII in H2 as [_[a[]]].
  apply R_Z'_Property in H3; auto with Z'.
  rewrite Z'_Mult_Property2 in H3; auto with Z'.
  set (two := (\[[F 2,F 0]\])). pose proof Z'0_in_Z'. pose proof Z'1_in_Z'.
  assert (Z'0 < Z'1); auto with Z'.
  assert (ω <> 0) as HH.
  { intro. pose proof in_ω_1. rewrite H7 in H8. elim (@ MKT16 1); auto. }
  assert (Z'1 < (two)).
  { rewrite Z'1_Property; auto. apply Z'_Ord_Instantiate; auto.
    rewrite (N'_Plus_Commutation (F 0)),N'_Plus_Property,N'_Plus_Property; auto.
    assert (Ensemble 1 /\ Ensemble 2) as [].
    { pose proof in_ω_1. pose proof in_ω_2. split; eauto. }
    apply (Const_is_Function ω) in H7 as [H7[]], H8 as [H8[]]; auto.
    pose proof in_ω_1; pose proof in_ω_2. apply Fn_in_N' in H13,H14.
    pose proof in_ω_1; pose proof in_ω_2. apply (F_Const_Fa F0 ω) in H15,H16; auto.
    assert (ran(Const 1) ⊂ ω /\ ran(Const 2) ⊂ ω) as [].
    { rewrite H10,H12. pose proof in_ω_1; pose proof in_ω_2.
      split; unfold Included; intros; apply MKT41 in H19; eauto;
      rewrite H19; auto. }
    rewrite <-H15,<-H16. apply N'_Ord_Instantiate; auto.
    assert (\{ λ w, (Const 1)[w] ∈ (Const 2)[w] \} = ω).
    { apply AxiomI; split; intros.
      - apply AxiomII in H19 as []. apply NNPP; intro.
        rewrite <-H9 in H21. apply MKT69a in H21.
        rewrite H21 in H20. elim MKT39; eauto.
      - apply AxiomII; split; eauto. pose proof H19.
        rewrite <-H9 in H19; rewrite <-H11 in H20.
        apply Property_Value,Property_ran in H19;
        apply Property_Value,Property_ran in H20; auto.
        rewrite H10 in H19; rewrite H12 in H20.
        pose proof in_ω_1; pose proof in_ω_2.
        apply MKT41 in H19; apply MKT41 in H20; eauto.
        rewrite H19,H20. apply MKT4; right. apply MKT41; eauto. }
    rewrite H19. destruct NPAUF as [[_[H20 _]]_].
    apply AxiomII in H20 as [H20[[]]]; tauto. }
  Z'split H1. assert (Z'0 < a).
  { assert (Z'0 ∈ Z' /\ a ∈ Z') as []; auto.
    apply (Z'_Ord_Tri _ a) in H10 as [H10|[|]]; auto; clear H11.
    apply (Z'_Mult_PrOrder _ _ two) in H10; auto.
    rewrite Z'_Mult_Property1 in H10; auto. unfold two in H10.
    rewrite <-H3 in H10. apply (Z'_Ord_Trans Z'0) in H10; auto.
    elim (Z'_Ord_irReflex Z'0 Z'0); auto. clear H11.
    apply (Z'_Ord_Trans Z'0) in H7; auto.
    rewrite <-H10,Z'_Mult_Property1 in H3; auto. elim Z'0_isnot_Z'1; auto. }
  apply (Z'_Mult_PrOrder _ _ a) in H7; auto.
  rewrite Z'_Mult_Property2,Z'_Mult_Commutation in H7; auto.
  unfold two in H7. rewrite <-H3 in H7. clear H8 H9.
  apply AxiomII in H2 as [H2[x[]]]. apply AxiomII in H8 as [H8[m[n[H11[]]]]].
  rewrite H9,H11,Z'1_Property in H7; auto.
  rewrite H9,H11,Z'0_Property in H10; auto.
  apply Z'_Ord_Instantiate in H7; apply Z'_Ord_Instantiate in H10; auto.
  rewrite N'_Plus_Property in H7; auto.
  rewrite N'_Plus_Commutation,N'_Plus_Property,
  N'_Plus_Commutation,N'_Plus_Property in H10; auto.
  apply AxiomII in H12 as [H12[f1[H14[H15[]]]]].
  apply AxiomII in H13 as [H13[f2[H18[H19[]]]]].
  assert (Ensemble 1). { pose proof in_ω_1. eauto. }
  apply (Const_is_Function ω) in H22 as [H22[]]; auto.
  pose proof in_ω_1. apply Fn_in_N' in H25. pose proof in_ω_1.
  assert (ran(Const 1) ⊂ ω).
  { unfold Included; intros. rewrite H24 in H27.
    apply MKT41 in H27; eauto. rewrite H27; auto. }
  rewrite H17,H21 in H7,H10. pose proof in_ω_1.
  apply (F_Const_Fa F0 ω) in H28; auto.
  rewrite <-H28,N'_Plus_Instantiate in H7; auto. pose proof H22.
  apply (ωFun_Plus_P1 f2) in H29 as [H29[]]; auto.
  apply N'_Ord_Instantiate in H7; apply N'_Ord_Instantiate in H10; auto.
  set (A := \{ λ w, f1[w] ∈ ((f2 + (Const 1))[w])%ωfun \}).
  set (B := \{ λ w, f2[w] ∈ f1[w] \}).
  assert (A ∩ B = 0).
  { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply MKT4' in H32 as []. apply AxiomII in H32 as [].
    apply AxiomII in H33 as []. rewrite ωFun_Plus_P2 in H34; auto.
    assert (z ∈ ω).
    { apply NNPP; intro. rewrite <-H19 in H36.
      apply MKT69a in H36. rewrite H36 in H35. elim MKT39; eauto. }
    assert (f1[z] ∈ ω /\ f2[z] ∈ ω) as [].
    { pose proof H36. rewrite <-H15 in H36. rewrite <-H19 in H37.
      apply Property_Value,Property_ran,H16 in H36; auto.
      apply Property_Value,Property_ran,H20 in H37; auto. }
    assert ((Const 1)[z] = PlusOne 0).
    { rewrite <-H23 in H36.
      apply Property_Value,Property_ran in H36; auto.
      rewrite H24 in H36. apply MKT41 in H36; eauto.
      rewrite H36. unfold PlusOne. rewrite MKT17; auto. }
    pose proof in_ω_0. rewrite H39,Plus_Property2_a,Plus_Property1_a
    in H34; auto. apply MKT4 in H34 as [].
    elim (MKT102 (f1[z]) (f2[z])); auto.
    apply MKT41 in H34; eauto. rewrite H34 in H35.
    elim (MKT101 (f2[z])); auto. }
  destruct NPAUF as [[_[]]_]. apply AxiomII in H33 as [H33[[H35[H36[H37[]]]]]].
  elim H36. rewrite <-H32. apply H38; auto.
  Close Scope z'_scope.
Qed.

(* 以下5条定义及结论旨在说明*Z与*Q_*Z是同构的.  *)
(* 构造: φ2是*Z到*Q_*Z的一一函数*)
Definition φ2 := \{\ λ u v, u ∈ Z' /\ v = \[[u,Z'1]\] \}\.

Property φ2_is_Function : Function1_1 φ2 /\ dom(φ2) = Z' /\ ran(φ2) = Q'_Z'.
Proof.
  intros. assert (Function1_1 φ2).
  { repeat split; unfold Relation; intros.
    - apply AxiomII in H as [H[x[y[]]]]; eauto.
    - apply AxiomII' in H as [H[]]. apply AxiomII' in H0 as [H0[]].
      rewrite H2,H4; auto.
    - apply AxiomII in H as [H[x[y[]]]]; eauto.
    - apply AxiomII' in H as []. apply AxiomII' in H1 as [H1[]].
      apply AxiomII' in H0 as []. apply AxiomII' in H4 as [H4[]].
      rewrite H3 in H6. apply R_Z'_Property in H6; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Commutation,Z'_Mult_Property2 in H6;
      auto with Z'. }
  split; auto. destruct H. split; apply AxiomI; split; intros.
  - apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2; tauto.
  - apply AxiomII; split; eauto. exists (\[[z,Z'1]\]).
    apply AxiomII'; split; auto. apply MKT49a; eauto.
    assert (\[[z,Z'1]\] ∈ Q').
    { apply Q'_Instantiate2; auto with Z'. } eauto.
  - apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2 as [H2[]].
    apply AxiomII; split; eauto.
  - pose proof H1. apply AxiomII; split; eauto.
    apply AxiomII in H2 as [_[a[]]]. exists a.
    apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Property φ2_Z'0 : φ2[Z'0] = Q'0.
Proof.
  destruct φ2_is_Function as [[][]]. pose proof Z'0_in_Z'. rewrite <-H1 in H3.
  apply Property_Value,AxiomII' in H3 as [_[]]; auto. rewrite H4,Q'0_Property; auto.
Qed.

Property φ2_Z'1 : φ2[Z'1] = Q'1.
Proof.
  destruct φ2_is_Function as [[][]]. pose proof Z'1_in_Z'. rewrite <-H1 in H3.
  apply Property_Value,AxiomII' in H3 as [_[]]; auto. rewrite H4,Q'1_Property; auto.
Qed.

(* φ2是序保持的:
   *Q_*Z 中元素的排序方式类似于 *Z 中元素的排序方式.  *)
Property φ2_PrOrder : ∀ a b, a ∈ Z' -> b ∈ Z' -> (a < b)%z' <-> φ2[a] < φ2[b].
Proof.
  intros. destruct φ2_is_Function as [[][]].
  assert (φ2[a] = \[[a,Z'1]\]).
  { rewrite <-H3 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φ2[b] = \[[b,Z'1]\]).
  { rewrite <-H3 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  rewrite H5,H6. clear H5 H6. split; intros.
  - apply Q'_Ord_Instantiate; auto with Z'.
    rewrite Z'_Mult_Property2,Z'_Mult_Commutation,
    Z'_Mult_Property2; auto with Z'.
  - apply Q'_Ord_Instantiate in H5; auto with Z'.
    rewrite Z'_Mult_Property2,Z'_Mult_Commutation,
    Z'_Mult_Property2 in H5; auto with Z'.
Qed.

(* φ2是加法保持的. *)
Property φ2_PrPlus : ∀ a b, a ∈ Z' -> b ∈ Z' -> φ2[(a + b)%z'] = φ2[a] + φ2[b].
Proof.
  intros. destruct φ2_is_Function as [[][]].
  assert (φ2[a] = \[[a,Z'1]\]).
  { rewrite <-H3 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φ2[b] = \[[b,Z'1]\]).
  { rewrite <-H3 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  rewrite H5,H6. rewrite Q'_Plus_Instantiate,Z'_Mult_Property2,
  Z'_Mult_Property2,Z'_Mult_Commutation,Z'_Mult_Property2; auto with Z'.
  assert ((a + b) ∈ Z')%z'; auto with Z'. rewrite <-H3 in H7.
  apply Property_Value in H7; auto. apply AxiomII' in H7; tauto.
Qed.

(* φ2是乘法保持的 *)
Property φ2_PrMult : ∀ a b, a ∈ Z' -> b ∈ Z' -> φ2[(a · b)%z'] = φ2[a] · φ2[b].
Proof.
  intros. destruct φ2_is_Function as [[][]].
  assert (φ2[a] = \[[a,Z'1]\]).
  { rewrite <-H3 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φ2[b] = \[[b,Z'1]\]).
  { rewrite <-H3 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  rewrite H5,H6. rewrite Q'_Mult_Instantiate,Z'_Mult_Property2; auto with Z'.
  assert ((a · b) ∈ Z')%z'; auto with Z'. rewrite <-H3 in H7.
  apply Property_Value in H7; auto. apply AxiomII' in H7; tauto.
Qed.
(* 综合以上5条定义及结论, 集*Q_*Z 与 集*Z 同构. *)

(* *Q_*N 实际上就是 *Q_*Z 大于等于零的部分. *)
Definition Q'_N' := \{ λ u, u ∈ Q'_Z' /\ (Q'0 = u \/ Q'0 < u) \}.

Property Q'_N'_is_Set : Ensemble Q'_N'.
Proof.
  apply (MKT33 Q'_Z'). apply Q'_Z'_is_Set; auto.
  unfold Included; intros. apply AxiomII in H; tauto.
Qed.

Property Q'_N'_propersubset_Q'_Z' : Q'_N' ⊂ Q'_Z' /\ Q'_N' <> Q'_Z'.
Proof.
  split.
  - unfold Included; intros. apply AxiomII in H; tauto.
  - intro. pose proof Q'1_in_Q'. pose proof H0.
    apply Q'_Neg in H1 as [x[[]_]]; auto. pose proof Z'1_in_Z'.
    pose proof H3. apply Z'_Neg in H4 as [u[[]_]]; auto.
    set (v := \[[u,Z'1]\]). assert (v ∈ Q').
    { apply Q'_Instantiate2; auto with Z'. }
    assert (Q'1 + v = Q'0).
    { unfold v. rewrite Q'1_Property,Q'_Plus_Instantiate,
      Z'_Mult_Property2,Z'_Mult_Commutation,Z'_Mult_Property2,
      H5,Q'0_Property; auto with Z'. }
    rewrite <-H2 in H7. apply Q'_Plus_Cancellation in H7; auto.
    assert (x < Q'0).
    { pose proof Q'0_in_Q'. pose proof Q'0_lt_Q'1.
      apply (Q'_Plus_PrOrder _ _ x) in H9; auto.
      rewrite Q'_Plus_Property,Q'_Plus_Commutation,H2 in H9; auto. }
    assert (x ∈ Q'_Z'). { rewrite <-H7. apply AxiomII; split; eauto. }
    rewrite <-H in H9. apply AxiomII in H9 as [_[_[]]].
    rewrite H9 in H8. elim (Q'_Ord_irReflex x x); auto.
    pose proof Q'0_in_Q'. apply (Q'_Ord_Trans x) in H9; auto.
    elim (Q'_Ord_irReflex x x); auto.
Qed.

Property Q'_N'_propersubset_Q' : Q'_N' ⊂ Q' /\ Q'_N' <> Q'.
Proof.
  split.
  - unfold Included; intros.
    apply Q'_Z'_propersubset_Q',Q'_N'_propersubset_Q'_Z'; auto.
  - intro. destruct Q'_Z'_propersubset_Q'. destruct Q'_N'_propersubset_Q'_Z'.
    elim H1. rewrite H in H2. apply AxiomI; split; auto.
Qed.

(* 将*N同构进*Q. *)
Definition φ3 := φ2 ∘ φ1.

Property φ3_is_Function : Function1_1 φ3 /\ dom(φ3) = N' /\ ran(φ3) ⊂ Q'.
Proof.
  destruct φ1_is_Function as [[][]]. destruct φ2_is_Function as [[][]].
  assert (Function1_1 φ3) as [].
  { split. apply MKT64; auto. unfold φ3. rewrite MKT62. apply MKT64; auto. }
  split; auto. split; auto. destruct Z'_N'_propersubset_Z' as [H9 _].
  rewrite <-H2,<-H5 in H9. split; try (apply AxiomI; split; intros).
  - apply AxiomII in H10 as [H10[y]]. apply AxiomII' in H11 as [H11[u[]]].
    apply Property_dom in H12. rewrite H1 in H12; auto.
  - apply AxiomII; split; eauto. rewrite <-H1 in H10.
    apply Property_Value in H10; auto. pose proof H10.
    apply Property_ran,H9,Property_Value in H11; auto.
    pose proof H10. apply Property_ran in H12.
    pose proof H11. apply Property_ran in H13.
    exists (φ2[φ1[z]]). apply AxiomII'; split; eauto.
    apply MKT49a; eauto. apply Property_dom in H10. eauto.
  - unfold Included; intros. apply AxiomII in H10 as [H10[]].
    apply AxiomII' in H11 as [H11[u[]]]. apply Property_ran in H13.
    rewrite H6 in H13. apply Q'_Z'_propersubset_Q'; auto.
Qed.

Lemma φ3_Lemma : ∀ M, M ∈ N' -> φ2[φ1[M]] = φ3[M].
Proof.
  intros. destruct φ1_is_Function as [[][]].
  destruct Z'_N'_propersubset_Z' as [H4 _]. destruct φ2_is_Function as [[][]].
  destruct Q'_Z'_propersubset_Q' as [H9 _]. rewrite <-H2 in H.
  apply Property_Value in H; auto. pose proof H. apply Property_ran in H10.
  rewrite H3 in H10. apply H4 in H10. rewrite <-H7 in H10.
  apply Property_Value in H10; auto. pose proof H10. apply Property_ran in H11.
  assert ([M,φ2[φ1[M]]] ∈ φ3).
  { apply AxiomII'; split; eauto. apply Property_dom in H. apply MKT49a; eauto. }
  destruct φ3_is_Function as [[][]]. apply Property_dom in H.
  rewrite H2,<-H15 in H. apply Property_Value in H; auto. destruct H13.
  apply (H17 M); auto.
Qed.

(* 关于φ3的两个实例.*)
Property φ3_N'0 : φ3[F 0] = Q'0.
Proof.
  intros. pose proof in_ω_0. apply Fn_in_N' in H. rewrite <-φ3_Lemma; auto.
  destruct φ1_is_Function as [[][]]. destruct φ2_is_Function as [[][]].
  rewrite <-H2 in H. apply Property_Value in H; auto. pose proof H.
  apply Property_ran in H8. rewrite H3 in H8.
  apply Z'_N'_propersubset_Z' in H8; auto. rewrite <-H6 in H8.
  apply Property_Value in H8; auto. apply AxiomII' in H as [H[]].
  apply AxiomII' in H8 as [H8[]].
  rewrite H10,<-Z'0_Property,<-Q'0_Property in H12; auto.
  rewrite H10,<-Z'0_Property; auto.
Qed.

Property φ3_N'1 : φ3[F 1] = Q'1.
Proof.
  intros. pose proof in_ω_1. apply Fn_in_N' in H. rewrite <-φ3_Lemma; auto.
  destruct φ1_is_Function as [[][]]. destruct φ2_is_Function as [[][]].
  rewrite <-H2 in H. apply Property_Value in H; auto. pose proof H.
  apply Property_ran in H8. rewrite H3 in H8.
  apply Z'_N'_propersubset_Z' in H8; auto. rewrite <-H6 in H8.
  apply Property_Value in H8; auto. apply AxiomII' in H as [H[]].
  apply AxiomII' in H8 as [H8[]].
  rewrite H10,<-Z'1_Property,<-Q'1_Property in H12; auto.
  rewrite H10,<-Z'1_Property; auto.
Qed.

(* φ3是序保持的 *)
Property φ3_PrOrder : ∀ M N, M ∈ N' -> N ∈ N' -> (M < N)%n' <-> φ3[M] < φ3[N].
Proof.
  intros. destruct φ1_is_Function as [[][]].
  pose proof H. apply (φ1_PrOrder M N) in H5; auto.
  destruct φ2_is_Function as [[][]]. pose proof H; pose proof H0.
  rewrite <-H3 in H10,H11. apply Property_Value,Property_ran in H10; auto.
  apply Property_Value,Property_ran in H11; auto. rewrite H4 in H10,H11.
  destruct Z'_N'_propersubset_Z' as [H12 _].
  apply H12 in H10; apply H12 in H11. pose proof H10.
  apply (φ2_PrOrder _ (φ1[N])) in H10; auto.
  rewrite (φ3_Lemma M),(φ3_Lemma N) in H10; auto.
  split; intros; [apply H10,H5|apply H5,H10]; auto.
Qed.

(* φ3是加法保持的 *)
Property φ3_PrPlus : ∀ M N, M ∈ N' -> N ∈ N' -> φ3[(M + N)%n'] = φ3[M] + φ3[N].
Proof.
  intros. destruct φ3_is_Function as [[][]]. pose proof H.
  apply (φ1_PrPlus M N) in H5; auto. destruct φ1_is_Function as [[][]].
  pose proof H; pose proof H0. rewrite <-H8 in H10,H11.
  apply Property_Value,Property_ran in H10; auto.
  apply Property_Value,Property_ran in H11; auto.
  rewrite H9 in H10,H11. destruct Z'_N'_propersubset_Z' as [H12 _].
  apply H12 in H10; apply H12 in H11. pose proof H10.
  apply (φ2_PrPlus _ (φ1[N])) in H13; auto.
  rewrite <-H5,(φ3_Lemma M),(φ3_Lemma N),φ3_Lemma in H13; auto.
  apply N'_Plus_in_N'; auto.
Qed.

(* φ3是乘法保持的 *)
Property φ3_PrMult : ∀ M N, M ∈ N' -> N ∈ N' -> φ3[(M · N)%n'] = φ3[M] · φ3[N].
Proof.
  intros. destruct φ3_is_Function as [[][]]. pose proof H.
  apply (φ1_PrMult M N) in H5; auto. destruct φ1_is_Function as [[][]].
  pose proof H; pose proof H0. rewrite <-H8 in H10,H11.
  apply Property_Value,Property_ran in H10; auto.
  apply Property_Value,Property_ran in H11; auto.
  rewrite H9 in H10,H11. destruct Z'_N'_propersubset_Z' as [H12 _].
  apply H12 in H10; apply H12 in H11. pose proof H10.
  apply (φ2_PrMult _ (φ1[N])) in H13; auto.
  rewrite <-H5,(φ3_Lemma M),(φ3_Lemma N),φ3_Lemma in H13; auto.
  apply N'_Mult_in_N'; auto.
Qed.

(* φ3 的值域为*Q_*N *)
Property φ3_ran : ran(φ3) = Q'_N'.
Proof.
  destruct φ3_is_Function as [[][]]. destruct φ1_is_Function as [[][]].
  destruct φ2_is_Function as [[][]]. destruct NPAUF as [[_[]]_].
  pose proof in_ω_0. apply Fn_in_N' in H13; auto. clear H11 H12.
  apply AxiomI; split; intros.
  - apply AxiomII in H11 as [H11[]]. pose proof H12.
    apply Property_dom,Property_Value in H14; auto.
    assert (z = φ3[x]). { destruct H. apply (H15 x); auto. }
    apply Property_dom in H12. pose proof H12. rewrite H1 in H12.
    rewrite H1,<-H5 in H16. apply Property_Value in H16; auto.
    pose proof H16. apply Property_ran in H17. rewrite H6 in H17.
    apply Z'_N'_propersubset_Z' in H17. rewrite <-H9 in H17.
    apply Property_Value in H17; auto. rewrite φ3_Lemma,<-H15 in H17; auto.
    apply Property_ran in H17. rewrite H10 in H17.
    apply AxiomII; repeat split; auto.
    assert ((F 0) ∈ N' /\ x ∈ N') as []; auto.
    apply (N'_Ord_Tri _ x) in H18 as [H18|[]]; auto; clear H19.
    + apply φ3_PrOrder in H18; auto. rewrite <-φ3_N'0,H15; auto.
    + elim (N'0_is_FirstMember x); auto.
    + rewrite <-H18,φ3_N'0 in H15; auto.
  - apply AxiomII in H11 as [H11[]]. pose proof H12.
    rewrite <-H10,reqdi in H15. apply Property_Value in H15; auto.
    apply AxiomII' in H15 as [].
    assert (((φ2⁻¹)[z]) ∈ Z'_N').
    { apply Property_dom in H16. rewrite H9 in H16. apply NNPP; intro.
      assert (((φ2⁻¹)[z]) ∈ (Z' ~ Z'_N')).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
      apply Z'_N'_Property2 in H18; auto. apply φ2_PrOrder in H18; auto with Z'.
      rewrite f11vi in H18; try rewrite H10; auto.
      assert (φ2[Z'0] = Q'0).
      { pose proof Z'0_in_Z'. rewrite <-H9 in H19.
        apply Property_Value in H19; auto. apply AxiomII' in H19 as [_[]].
        rewrite H20,Q'0_Property; auto. }
      rewrite H19 in H18. apply Q'_Z'_propersubset_Q' in H12; auto.
      pose proof Q'0_in_Q'. destruct H14. rewrite H14 in H18.
      elim (Q'_Ord_irReflex z z); auto. apply (Q'_Ord_Trans z) in H14; auto.
      elim (Q'_Ord_irReflex z z); auto. }
    rewrite <-H6,reqdi in H17. apply Property_Value in H17; auto.
    apply AxiomII' in H17 as []. pose proof H18. apply Property_dom in H19.
    apply AxiomII; split; auto. exists ((φ1⁻¹)[(φ2⁻¹)[z]]).
    apply AxiomII'; split; eauto.
Qed.
(* *N已被同构嵌入*Q中 *)

Property Q'_N'_Q'0_is_FirstMember: ∀ u, u ∈ Q'_N' -> u <> Q'0 -> Q'0 < u.
Proof.
  intros. pose proof Q'0_in_Q'. pose proof H. apply Q'_N'_propersubset_Q' in H2.
  pose proof H1. apply (Q'_Ord_Tri _ u) in H3 as [|[|]]; auto.
  - apply AxiomII in H as [_[H[]]]; auto.
    rewrite H4 in H3. elim (Q'_Ord_irReflex u u); auto.
  - elim H0; auto.
Qed.

