(*    This file presents the formalization of rational numbers in R.    *)
(*   It is developmented in the CoqIDE (version 8.13.2) for windows.    *)

(** N_Z_Q_in_R *)

Require Export fmcr.Qs_to_R.

(* 上一节中已经在 *Q_Arch 中找到 *Q_N, R中的N实际上就是 *Q_N中的元素扩张而来. *)
Definition Ｎ := \{ λ u, ∃ n, n ∈ Q'_N /\ u = \[n\] \}.

Property N_is_Set : Ensemble Ｎ.
Proof.
  apply (MKT33 Ｒ). apply R_is_Set. unfold Included; intros.
  apply AxiomII in H as [H[x[]]]. rewrite H1. apply R_Instantiate2; auto.
  apply Q'_N_propersubset_Q'_Arch; auto.
Qed.

Property N_propersubset_R : Ｎ ⊂ Ｒ /\ Ｎ <> Ｒ.
Proof.
  split.
  - unfold Included; intros. apply AxiomII in H as [H[x[]]].
    rewrite H1. apply R_Instantiate2; auto.
    apply Q'_N_propersubset_Q'_Arch; auto.
  - intro. pose proof R1_in_R. unfold R1 in H0. pose proof Q'1_in_Q'_N.
    pose proof H1. apply Q'_N_propersubset_Q'_Arch in H2; auto. pose proof H2.
    apply Q'_Arch_subset_Q' in H3; auto. pose proof H3.
    apply Q'_Neg in H4 as [n0[[]_]]; auto.
    assert (n0 ∈ Q'_Arch).
    { destruct NPAUF as [_]. apply NNPP; intro.
      assert (n0 ∈ (Q' ~ Q'_Arch)).
      { apply MKT4'; split; auto. apply AxiomII; eauto. }
      apply (infinity_Plus_finity _ Q'1) in H8; auto with Q'.
      rewrite Q'_Plus_Commutation,H5 in H8; auto with Q'.
      apply MKT4' in H8 as []. apply AxiomII in H9 as []. elim H10.
      apply Q'0_in_Q'_Arch; auto. }
    assert (\[n0\] ∈ Ｒ). { apply R_Instantiate2; auto. }
    rewrite <-H in H7. apply AxiomII in H7 as [H7[m[]]].
    pose proof H8. apply Q'_N_propersubset_Q'_Arch in H10; auto.
    pose proof H10. apply Q'_Arch_subset_Q' in H11; auto.
    symmetry in H9. apply R_Q'_Property in H9; auto.
    assert (m - n0 = m + Q'1)%q'.
    { rewrite Q'_Plus_Commutation in H5; auto.
      apply Q'_Minus_Plus in H5; auto with Q'.
      rewrite <-H5,<-Q'_Mix_Association1,Q'_Plus_Property; auto with Q'. }
    assert (Q'1 = (m + Q'1) \/ Q'1 < (m + Q'1))%q'.
    { destruct (classic (m = Q'0)).
      - left. rewrite H13,Q'_Plus_Commutation,Q'_Plus_Property; auto with Q'.
      - assert (m ∈ (Q'_N ~ [Q'0])).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto.
          intro. apply MKT41 in H14; auto. pose proof Q'0_in_Q'. eauto. }
        apply Q'_N_Q'0_is_FirstMember in H14; auto.
        apply (Q'_Plus_PrOrder _ _ Q'1) in H14; auto with Q'.
        rewrite Q'_Plus_Property,Q'_Plus_Commutation in H14; auto. }
    assert (Q'0 < (m + Q'1))%q'.
    { destruct H13.
      - rewrite <-H13. apply Q'0_lt_Q'1; auto.
      - apply (Q'_Ord_Trans Q'0) in H13; auto with Q'. }
    apply mt_Q'0_Q'Abs in H14; auto with Q'. apply AxiomII in H9 as [H9[]].
    assert (Q'1 ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. pose proof Q'0_in_Q'. apply MKT41 in H17; eauto.
      elim Q'0_isnot_Q'1; auto. }
    apply H16 in H17. rewrite H12,H14,Q'_Divide_Property2 in H17; auto.
    destruct H13.
    + rewrite <-H13 in H17. elim (Q'_Ord_irReflex Q'1 Q'1); auto.
    + apply (Q'_Ord_Trans Q'1) in H17; auto with Q'.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto.
Qed.

(* 定义一个函数: 以证明 *Q_N 与 N 同构 *)
Definition φn := \{\ λ u v, u ∈ Q'_N /\ v = \[u\] \}\.

Open Scope q'_scope.

(* 以下两个引理为证明φn是一一函数做准备.*)
Lemma φn_is_Function_Lemma1 : ∀ u v, u ∈ Q'_N -> v ∈ Q'_N
  -> (v < u) -> Q'1 = |(u - v)| \/ Q'1 < |(u - v)|.
Proof.
  intros. destruct φ4_is_Function as [[][]].
  assert (u ∈ ran(φ4) /\ v ∈ ran(φ4)) as []; auto. rewrite reqdi in H6,H7.
  apply Property_Value,Property_ran in H6;
  apply Property_Value,Property_ran in H7; auto. rewrite <-deqri,H4 in H6,H7.
  assert (v = φ4[(φ4⁻¹)[v]] /\ u = φ4[(φ4⁻¹)[u]]) as [].
  { split; rewrite f11vi; auto. }
  pose proof H1. rewrite H8,H9 in H10. apply φ4_PrOrder in H10; auto.
  apply Plus_PrOrder_Corollary in H10 as [n[[H10[]]_]]; auto.
  pose proof H10. apply (φ4_PrPlus ((φ4⁻¹)[v]) n) in H13; auto.
  rewrite H12,f11vi,f11vi in H13; auto. clear H12.
  assert ((φ4[n]) ∈ Q'_N).
  { rewrite <-H4 in H10. apply Property_Value,Property_ran in H10; auto. }
  assert (Q'0 < φ4[n]).
  { apply φ4_PrOrder in H11; auto. rewrite φ4_0 in H11; auto. }
  assert (|(u - v)| = φ4[n]).
  { assert (u - v = φ4[n]). { apply Q'_Minus_Plus; auto. }
    rewrite H15. apply mt_Q'0_Q'Abs; auto. }
  rewrite H15. pose proof in_ω_0. pose proof in_ω_1.
  assert (1 = n \/ 1 ∈ n).
  { assert (Ordinal 1 /\ Ordinal n) as [].
    { apply AxiomII in H17 as [H17[]]. apply AxiomII in H10 as [H10[]]; auto. }
    apply (@ MKT110 1 n) in H18 as [H18|[]]; auto; clear H19.
    apply MKT41 in H18; eauto. rewrite H18 in H11. elim (@ MKT16 0); auto. }
  destruct H18.
  - left. rewrite <-H18,φ4_1; auto.
  - right. apply φ4_PrOrder in H18; auto. rewrite <-φ4_1; auto.
Qed.

Close Scope q'_scope.

Lemma φn_is_Function_Lemma2 : ∀ u v, u ∈ Q'_N -> v ∈ Q'_N -> u <> v
  -> \[u\] <> \[v\].
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_N_propersubset_Q'_Arch in H2;
  apply Q'_N_propersubset_Q'_Arch in H3; auto.
  pose proof H; pose proof H0.
  apply Q'_N_propersubset_Q'_Arch,Q'_Arch_subset_Q' in H4;
  apply Q'_N_propersubset_Q'_Arch,Q'_Arch_subset_Q' in H5; auto.
  assert (Q'1 ∈ (Q'_N ~ [Q'0])).
  { pose proof Q'1_in_Q'_N. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. intro. pose proof Q'0_in_Q'.
    apply MKT41 in H7; eauto. elim Q'0_isnot_Q'1; auto. }
  assert (u ∈ Q' /\ v ∈ Q') as []; auto.
  apply (Q'_Ord_Tri u v) in H7 as [H7|[]]; try contradiction; auto; clear H8; intro.
  - symmetry in H8. apply R_Q'_Property in H8; auto.
    apply AxiomII in H8 as [H8[]]. apply H10 in H6.
    rewrite Q'_Divide_Property2 in H6; auto with Q'.
    pose proof H7. apply φn_is_Function_Lemma1 in H11 as []; auto.
    + rewrite <-H11 in H6.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
    + apply (Q'_Ord_Trans Q'1) in H6; auto with Q'.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
  - apply R_Q'_Property in H8; auto. apply AxiomII in H8 as [H8[]].
    apply H10 in H6. rewrite Q'_Divide_Property2 in H6; auto with Q'.
    pose proof H7. apply φn_is_Function_Lemma1 in H11 as []; auto.
    + rewrite <-H11 in H6. elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
    + apply (Q'_Ord_Trans Q'1) in H6; auto with Q'.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
Qed.

(* φn是一一函数 定义域为 *Q_N 值域是N. *)
Property φn_is_Function : Function1_1 φn /\ dom(φn) = Q'_N /\ ran(φn) = Ｎ.
Proof.
  assert (Function1_1 φn).
  { repeat split; intros.
    - unfold Relation; intros. apply AxiomII in H as [H[u[v[]]]]; eauto.
    - apply AxiomII' in H as [H1[]]; apply AxiomII' in H0 as [H0[]].
      rewrite H2,H4; auto.
    - unfold Relation; intros. apply AxiomII in H as [H[u[v[]]]]; eauto.
    - apply AxiomII' in H as []; apply AxiomII' in H0 as [].
      apply AxiomII' in H1 as [H1[]]; apply AxiomII' in H2 as [H2[]].
      destruct (classic (y = z)); auto. apply φn_is_Function_Lemma2 in H7; auto.
      elim H7. rewrite <-H4,<-H6; auto. }
  split; auto. destruct H. split.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2; tauto.
    + apply AxiomII; split. eauto. exists (\[z\]). pose proof H1.
      apply Q'_N_propersubset_Q'_Arch,(R_Instantiate2 z) in H2.
      apply AxiomII'; split; auto. apply MKT49a; eauto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2 as [H2[]].
      rewrite H4. apply AxiomII; split; eauto. rewrite <-H4; auto.
    + apply AxiomII; split. eauto. apply AxiomII in H1 as [H1[x[]]].
      exists x. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Property φn_Q'0 : φn[Q'0] = R0.
Proof.
  destruct φn_is_Function as [[][]]. pose proof Q'0_in_Q'_N.
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3 as [_[]]; auto.
Qed.

Property φn_Q'1 : φn[Q'1] = R1.
Proof.
  intros. destruct φn_is_Function as [[][]]. pose proof Q'1_in_Q'_N.
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3 as [_[]]; auto.
Qed.

(* φn是序保持的. *)
Property φn_PrOrder : ∀ u v, u ∈ Q'_N -> v ∈ Q'_N
  -> (u < v)%q' <-> φn[u] < φn[v].
Proof.
  intros. destruct φn_is_Function as [[][]].
  assert (φn[u] = \[u\]).
  { rewrite <-H3 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φn[v] = \[v\]).
  { rewrite <-H3 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  pose proof H; pose proof H0.
  apply Q'_N_propersubset_Q'_Arch in H7;
  apply Q'_N_propersubset_Q'_Arch in H8; auto.
  pose proof H7; pose proof H8.
  apply Q'_Arch_subset_Q' in H9; apply Q'_Arch_subset_Q' in H10; auto.
  rewrite H5,H6. split; intros.
  - assert (u <> v).
    { intro. rewrite H12 in H11.
      elim (Q'_Ord_irReflex v v); auto. }
    apply Q'_Ord_to_R_Ord in H11 as []; auto.
    apply φn_is_Function_Lemma2 in H12; auto; try contradiction.
  - apply R_Ord_Instantiate in H11; tauto.
Qed.

(* φn是加法保持的. *)
Property φn_PrPlus : ∀ u v, u ∈ Q'_N -> v ∈ Q'_N
  -> φn[(u + v)%q'] = φn[u] + φn[v].
Proof.
  intros. pose proof H. apply (Q'_N_Plus_in_Q'_N u v) in H1; auto.
  destruct φn_is_Function as [[][]]. rewrite <-H4 in H1.
  apply Property_Value in H1; auto. apply AxiomII' in H1 as [H1[]].
  assert (φn[u] = \[u\]).
  { rewrite <-H4 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φn[v] = \[v\]).
  { rewrite <-H4 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  rewrite H7,H8,H9,R_Plus_Instantiate; try apply Q'_N_propersubset_Q'_Arch; auto.
Qed.

(* φn是乘法保持的. *)
Property φn_PrMult : ∀ u v, u ∈ Q'_N -> v ∈ Q'_N
  -> φn[(u · v)%q'] = φn[u] · φn[v].
Proof.
  intros. pose proof H. apply (Q'_N_Mult_in_Q'_N u v) in H1; auto.
  destruct φn_is_Function as [[][]]. rewrite <-H4 in H1.
  apply Property_Value in H1; auto. apply AxiomII' in H1 as [H1[]].
  assert (φn[u] = \[u\]).
  { rewrite <-H4 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φn[v] = \[v\]).
  { rewrite <-H4 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  rewrite H7,H8,H9,R_Mult_Instantiate; try apply Q'_N_propersubset_Q'_Arch; auto.
Qed.

Property R0_in_N : R0 ∈ Ｎ.
Proof.
  pose proof R0_in_R. apply AxiomII; split; eauto. exists Q'0.
  split; auto. apply Q'0_in_Q'_N; auto.
Qed.

Global Hint Resolve R0_in_N : R.

Property R1_in_N : R1 ∈ Ｎ.
Proof.
  pose proof R1_in_R. apply AxiomII; split; eauto. exists Q'1.
  split; auto. apply Q'1_in_Q'_N; auto.
Qed.

Global Hint Resolve R1_in_N : R.

(* N对加法封闭. *)
Property N_Plus_in_N : ∀ u v, u ∈ Ｎ -> v ∈ Ｎ -> (u + v) ∈ Ｎ.
Proof.
  intros. pose proof H; pose proof H0.
  apply N_propersubset_R in H1; apply N_propersubset_R in H2; auto.
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H0 as [H0[y[]]].
  pose proof H1. apply (R_Plus_in_R u v) in H7; auto.
  apply AxiomII; split; eauto. exists (x + y)%q'.
  split. apply Q'_N_Plus_in_Q'_N; auto.
  rewrite H4,H6,R_Plus_Instantiate; try apply Q'_N_propersubset_Q'_Arch; auto.
Qed.

Global Hint Resolve N_Plus_in_N : R.

(* N对乘法封闭. *)
Property N_Mult_in_N : ∀ u v, u ∈ Ｎ -> v ∈ Ｎ -> (u · v) ∈ Ｎ.
Proof.
  intros. pose proof H; pose proof H0.
  apply N_propersubset_R in H1; apply N_propersubset_R in H2; auto.
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H0 as [H0[y[]]].
  pose proof H1. apply (R_Mult_in_R u v) in H7; auto.
  apply AxiomII; split; eauto. exists (x · y)%q'. split.
  apply Q'_N_Mult_in_Q'_N; auto.
  rewrite H4,H6,R_Mult_Instantiate; try apply Q'_N_propersubset_Q'_Arch; auto.
Qed.

Global Hint Resolve N_Mult_in_N : R.

(* R中定义的序对于N是良序的 *)
Property R_Ord_WellOrder_N : WellOrdered R_Ord Ｎ.
Proof.
  split; intros.
  - unfold Connect; intros. apply R_Ord_Tri; auto; apply N_propersubset_R; auto.
  - pose proof Q'_Ord_WellOrder_Q'_N. destruct φn_is_Function as [[][]].
    assert (Q'_N = φn⁻¹「Ｎ」).
    { apply AxiomI; split; intros.
      - apply AxiomII; repeat split; eauto. rewrite H4; auto.
        rewrite <-H4 in H6. apply Property_Value,Property_ran in H6; auto.
        rewrite <-H5; auto.
      - apply AxiomII in H6 as [H6[]]. rewrite <-H4; auto. }
    assert (φn⁻¹「y」 ⊂ Q'_N /\ φn⁻¹「y」 <> Φ) as [].
    { split.
      - unfold Included; intros. apply AxiomII in H7 as [_[]].
        rewrite H4 in H7; auto.
      - apply PreimageSet_Fact; auto. rewrite H5. intro. elim H0.
        apply AxiomI; split; intros. pose proof H8. apply H in H9.
        assert (z ∈ (y ∩ Ｎ)). { apply MKT4'; auto. }
        rewrite <-H7; auto. elim (@ MKT16 z); auto. }
    apply H1 in H7 as [x[]]; auto; clear H8. exists (φn[x]). split.
    + apply AxiomII in H7; tauto.
    + intros. assert ((φn⁻¹)[y0] ∈ φn⁻¹「y」).
      { pose proof H8 as H8'. apply H in H8. rewrite <-H5,reqdi in H8.
        apply Property_Value,Property_ran in H8; auto.
        rewrite <-deqri in H8. apply AxiomII; repeat split; eauto.
        rewrite f11vi; auto. rewrite H5; auto. }
      pose proof H10. apply H9 in H10. intro. elim H10.
      apply φn_PrOrder; auto. apply AxiomII in H11 as [_[]].
      rewrite <-H4; auto. apply AxiomII in H7 as [_[]].
      rewrite <-H4; auto. rewrite f11vi; auto. rewrite H5. apply H; auto.
Qed.

(* R0是N中首元 *)
Property N_R0_is_FirstMember : ∀ u, u ∈ Ｎ -> u <> R0 -> R0 < u.
Proof.
  intros. destruct φn_is_Function as [[][]]. pose proof H. rewrite <-H4 in H5.
  pose proof H5. rewrite reqdi in H5. apply Property_Value,Property_ran in H5;
  auto. rewrite <-deqri,H3 in H5.
  assert ((φn⁻¹)[u] ∈ (Q'_N ~ [Q'0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H7; eauto with Q'. pose proof φn_Q'0.
    rewrite <-H7,f11vi in H8; auto. }
  apply Q'_N_Q'0_is_FirstMember in H7; auto.
  apply φn_PrOrder in H7; try apply Q'0_in_Q'_N; auto.
  rewrite φn_Q'0,f11vi in H7; auto.
Qed.
(* 至此, ω  *N_N  *Q_N  N 这四个集合相互间均是同构的, 
   选取其中任意一个都可以作为自然数集使用. *)

(* 接下来寻找R中的Z. 构建Z的思路与构建N相同, 由 *Q_Arch中的Z(即 *Q_Z)扩张而来. *)
Definition Ｚ := \{ λ u, ∃ z, z ∈ Q'_Z /\ u = \[z\] \}.

Property Z_is_Set : Ensemble Ｚ.
Proof.
  apply (MKT33 Ｒ). apply R_is_Set; auto. unfold Included; intros.
  apply AxiomII in H as [H[x[]]]. rewrite H1. apply R_Instantiate2; auto.
  apply Q'_Z_propersubset_Q'_Arch; auto.
Qed.

(* 整数集是实数集的真子集 *)
Property Z_propersubset_R : Ｚ ⊂ Ｒ /\ Ｚ <> Ｒ.
Proof.
  Open Scope q'_scope.
  split.
  - unfold Included; intros. apply AxiomII in H as [H[x[]]].
    rewrite H1. apply R_Instantiate2; auto.
    apply Q'_Z_propersubset_Q'_Arch; auto.
  - intro. set (two := (Z'1 + Z'1)%z').
    assert (two ∈ (Z' ~ [Z'0])).
    { assert ((Z'1 + Z'1)%z' ∈ Z'); auto with Z'.
      apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. pose proof Z'0_in_Z'. apply MKT41 in H1; eauto.
      pose proof Z'0_lt_Z'1. pose proof H3.
      apply (Z'_Plus_PrOrder _ _ Z'1) in H4; auto with Z'. unfold two in H1.
      rewrite Z'_Plus_Property,H1 in H4; auto with Z'.
      apply (Z'_Ord_Trans Z'0) in H4; auto with Z'.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'. }
    set (dw := \[[Z'1,two]\]). Z'split H0.
    assert (Z'0 < two)%z'.
    { unfold two. apply (Z'_Ord_Trans _ Z'1); auto with Z'.
      pose proof Z'0_lt_Z'1.
      apply (Z'_Plus_PrOrder _ _ Z'1) in H3; auto with Z'.
      rewrite Z'_Plus_Property in H3; auto with Z'. }
    assert (dw ∈ Q'). { apply Q'_Instantiate2; auto with Z'. }
    assert (Q'0 < dw).
    { rewrite Q'0_Property; auto. unfold dw.
      apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Commutation,Z'_Mult_Property1,
      Z'_Mult_Property2; auto with Z'. }
    assert (dw < Q'1).
    { unfold dw. rewrite Q'1_Property; auto.
      apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Property2; auto with Z'.
      replace Z'1 with (Z'1 + Z'0)%z'.
      unfold two. apply Z'_Plus_PrOrder; auto with Z'.
      apply Z'_Plus_Property; auto with Z'. }
    assert (dw ∈ Q'_Arch).
    { apply AxiomII; repeat split; eauto. exists Q'1.
      apply mt_Q'0_Q'Abs in H5; auto. rewrite H5.
      split; auto. apply Q'1_in_Q'_N; auto. }
    assert (\[dw\] ∈ Ｒ)%r. { apply R_Instantiate2; auto. }
    rewrite <-H in H8. apply AxiomII in H8 as [H8[x[]]].
    set (qtwo := Q'1 + Q'1).
    assert (qtwo ∈ Q'). { unfold qtwo; auto with Q'. }
    assert (qtwo ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split. apply Q'_N_Plus_in_Q'_N;
      try apply Q'1_in_Q'_N; auto. apply AxiomII; split; eauto.
      intro. pose proof Q'0_in_Q'. apply MKT41 in H12; eauto.
      pose proof Q'0_lt_Q'1. rewrite <-H12 in H14.
      replace Q'1 with (Q'1 + Q'0) in H14.
      unfold qtwo in H14. apply Q'_Plus_PrOrder in H14; auto with Q'.
      pose proof Q'0_lt_Q'1.
      apply (Q'_Ord_Trans Q'1) in H15; auto with Q'.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
      apply Q'_Plus_Property; auto with Q'. }
    assert (dw · qtwo = Q'1).
    { unfold qtwo. rewrite Q'_Mult_Distribution,Q'_Mult_Property2;
      auto with Q'. unfold dw. rewrite Q'_Plus_Instantiate,
      Z'_Mult_Property2,Z'_Mult_Commutation,Z'_Mult_Property2,
      Q'1_Property; auto with Z'. apply R_Z'_Property; auto with Z'.
      assert (two · two = two + two)%z'.
      { unfold two. rewrite Z'_Mult_Distribution,Z'_Mult_Property2;
        auto with Z'. } rewrite H13; auto. }
    assert (Q'0 < qtwo).
    { apply (Q'_Ord_Trans _ Q'1); auto with Q'. replace Q'1 with (Q'1 + Q'0).
      apply Q'_Plus_PrOrder; auto with Q'. apply Q'_Plus_Property; auto with Q'. }
    pose proof H9. apply Q'_Z_propersubset_Q'_Arch in H15; auto.
    pose proof H9. apply Q'_Z_subset_Q' in H16; auto.
    assert (Q'0 < x).
    { assert (Q'0 ∈ Q' /\ x ∈ Q') as []. { split; auto with Q'. }
      apply (Q'_Ord_Tri _ x) in H17 as [H17|[]]; auto; clear H18.
      - pose proof H17. apply Q'_Plus_PrOrder_Corollary in H18
        as [x0[[H18[]]_]]; auto with Q'.
        assert (dw - x = dw + x0).
        { apply Q'_Minus_Plus; auto with Q'.
          rewrite (Q'_Plus_Commutation _ x0),
          <-Q'_Plus_Association,H20,Q'_Plus_Commutation,
          Q'_Plus_Property; auto with Q'. }
        pose proof H19. apply (Q'_Plus_PrOrder _ _ dw) in H22; auto with Q'.
        rewrite Q'_Plus_Property in H22; auto.
        apply (Q'_Ord_Trans Q'0) in H22; auto with Q'.
        pose proof H22. apply mt_Q'0_Q'Abs in H23; auto with Q'.
        apply R_Q'_Property in H10; auto.
        apply AxiomII in H10 as [_[]]. apply H24 in H12.
        rewrite H21,H23 in H12. rewrite Q'_Mult_Commutation in H13; auto.
        apply Q'_Divide_Mult in H13; auto with Q'. rewrite H13 in H12.
        replace x with (x + Q'0). rewrite <-H20.
        apply Q'_Plus_PrOrder; auto with Q'.
        rewrite H20. apply (Q'_Plus_PrOrder _ _ dw); auto with Q'.
        rewrite Q'_Plus_Property; auto. rewrite Q'_Plus_Property; auto.
        intro. rewrite H26 in H14. elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'.
      - apply R_Q'_Property in H10; auto. assert (dw - x = dw).
        { apply Q'_Minus_Plus; auto. rewrite Q'_Plus_Commutation; auto.
          rewrite <-H17. apply Q'_Plus_Property; auto. }
        rewrite H18 in H10. clear H18. apply AxiomII in H10 as [_[]].
        apply H18 in H12. apply mt_Q'0_Q'Abs in H5; auto. rewrite H5 in H12.
        rewrite Q'_Mult_Commutation in H13; auto.
        apply Q'_Divide_Mult in H13; auto with Q'.
        rewrite H13 in H12. elim (Q'_Ord_irReflex dw dw); auto. intro.
        rewrite H20 in H14. elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
    assert (x < Q'1).
    { assert (x ∈ Q' /\ Q'1 ∈ Q') as []. { split; auto with Q'. }
      apply (Q'_Ord_Tri x Q'1) in H18 as []; auto; clear H19.
      assert (Q'0 < (x - dw)).
      { apply (Q'_Plus_PrOrder _ _ dw); auto with Q'.
        rewrite Q'_Plus_Property,<-Q'_Mix_Association1,
        Q'_Plus_Commutation,Q'_Mix_Association1; auto with Q'.
        replace (dw - dw) with Q'0. rewrite Q'_Plus_Property; auto. destruct H18.
        - apply (Q'_Ord_Trans _ Q'1); auto with Q'.
        - rewrite H18; auto.
        - symmetry. apply Q'_Minus_Plus; auto with Q'.
          apply Q'_Plus_Property; auto. }
      pose proof H19. apply mt_Q'0_Q'Abs in H20; auto with Q'.
      symmetry in H10. apply R_Q'_Property in H10; auto.
      apply AxiomII in H10 as [_[]]. apply H21 in H12.
      rewrite H20 in H12. rewrite Q'_Mult_Commutation in H13; auto.
      apply Q'_Divide_Mult in H13; auto with Q'.
      rewrite H13 in H12. apply (Q'_Plus_PrOrder _ _ (dw)) in H12; auto.
      rewrite <-Q'_Mix_Association1,(Q'_Plus_Commutation dw),Q'_Mix_Association1,
      Q'_Minus_Property1,Q'_Plus_Property in H12; auto.
      replace Q'1 with (dw + dw); auto.
      - unfold dw. rewrite Q'_Plus_Instantiate; auto with Z'.
        rewrite Z'_Mult_Property2,Z'_Mult_Commutation,
        Z'_Mult_Property2; auto with Z'. rewrite Q'1_Property; auto.
        apply R_Z'_Property; auto with Z'.
        rewrite Z'_Mult_Property2,Z'_Mult_Property2; auto with Z'.
        unfold two. rewrite Z'_Mult_Distribution,
        Z'_Mult_Property2; auto with Z'.
      - intro. rewrite H23 in H14.
        elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
    assert (x ∈ Q'_N).
    { rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; split; eauto. }
    destruct φ4_is_Function as [[][]]. assert (x ∈ ran(φ4)); auto.
    rewrite reqdi in H24. apply Property_Value,Property_ran in H24; auto.
    rewrite <-deqri,H22 in H24. assert (φ4[(φ4⁻¹)[x]] = x). { rewrite f11vi; auto. }
    pose proof in_ω_0; pose proof in_ω_1.
    rewrite <-φ4_0,<-H25 in H17; auto. apply φ4_PrOrder in H17; auto.
    rewrite <-φ4_1,<-H25 in H18; auto. apply φ4_PrOrder in H18; auto.
    apply MKT41 in H18; eauto. rewrite H18 in H17. elim (@ MKT16 0); auto.
  Close Scope q'_scope.
Qed.

(* 定义一个函数: 以证明 *Q_Z 与 Z 同构 *)
Definition φz := \{\ λ u v, u ∈ Q'_Z /\ v = \[u\] \}\.

Open Scope q'_scope.

(* 以下两个引理为证明φz是一一函数做准备.*)
Lemma φz_is_Function_Lemma1 : ∀ u v, u ∈ Q'_Z -> v ∈ Q'_Z -> v < u
  -> Q'1 = |(u - v)| \/ Q'1 < |(u - v)|.
Proof.
  intros. pose proof H. pose proof H0.
  apply Q'_Z_subset_Q' in H2; apply Q'_Z_subset_Q' in H3; auto.
  assert (|(u - v)| = u - v).
  { pose proof H1.
    apply Q'_Plus_PrOrder_Corollary in H4 as [x[[H4[]]_]]; auto.
    apply Q'_Minus_Plus in H6; auto.
    apply mt_Q'0_Q'Abs in H5; auto. rewrite H6; auto. }
  pose proof Q'0_in_Q'; pose proof Q'1_in_Q'.
  assert (Q'0 ∈ Q' /\ u ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ u) in H7; auto; clear H8.
  assert (Q'0 ∈ Q' /\ v ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ v) in H8; auto; clear H9.
  destruct H7 as [H7|[]].
  - assert (u ∈ Q'_N).
    { rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; split; eauto. }
    assert (Q'1 = u \/ Q'1 < u).
    { assert (u = u - Q'0). { rewrite Q'_Minus_Property2; auto. }
      pose proof H7. apply mt_Q'0_Q'Abs in H7; auto. rewrite <-H7,H10.
      apply φn_is_Function_Lemma1; auto. apply Q'0_in_Q'_N; auto. }
    destruct H8 as [H8|[]].
    + assert (v ∈ Q'_N).
      { rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; split; eauto. }
      apply φn_is_Function_Lemma1; auto.
    + apply Q'_Plus_PrOrder_Corollary in H8 as [v0[[H8[]]_]]; auto.
      assert (u - v = u + v0).
      { apply Q'_Minus_Plus; auto with Q'.
        rewrite (Q'_Plus_Commutation u),<-Q'_Plus_Association,
        H12,Q'_Plus_Commutation,Q'_Plus_Property; auto. }
      right. rewrite H4,H13. destruct H10.
      * apply (Q'_Plus_PrOrder _ _ u) in H11; auto.
        rewrite Q'_Plus_Property in H11; auto. rewrite H10; auto.
      * apply (Q'_Plus_PrOrder _ _ u) in H11; auto.
        rewrite Q'_Plus_Property in H11; auto.
        apply (Q'_Ord_Trans _ u); auto with Q'.
    + assert (u - v = u).
      { apply Q'_Minus_Plus; auto.
        rewrite Q'_Plus_Commutation,<-H8,Q'_Plus_Property; auto. }
      rewrite H4,H11; auto.
  - destruct H8 as [H8|[]].
    + apply (Q'_Ord_Trans u),(Q'_Ord_Trans v) in H8; auto.
      elim (Q'_Ord_irReflex v v); auto.
    + assert (u ∈ \{ λ u, u ∈ Q'_Z /\ u < Q'0 \}
        /\ v ∈ \{ λ u, u ∈ Q'_Z /\ u < Q'0 \}).
      { split; apply AxiomII; split; eauto. } destruct H9.
      rewrite Q'_N_Neg_equ_Q'_Z_lt_Q'0 in H9,H10; auto.
      apply AxiomII in H9 as [_[_[u0[]]]].
      apply AxiomII in H10 as [_[_[v0[]]]].
      assert (u0 ∈ Q'_N /\ v0 ∈ Q'_N) as [].
      { apply MKT4' in H9 as []; apply MKT4' in H10 as []; auto. }
      pose proof H13; pose proof H14.
      apply Q'_N_propersubset_Q'_Arch,Q'_Arch_subset_Q' in H13;
      apply Q'_N_propersubset_Q'_Arch,Q'_Arch_subset_Q' in H14; auto.
      assert (u - v = v0 - u0).
      { apply Q'_Minus_Plus; auto with Q'.
        rewrite <-Q'_Mix_Association1,H12; auto. apply Q'_Minus_Plus; auto.
        rewrite Q'_Plus_Commutation; auto. }
      assert (u0 < v0).
      { apply (Q'_Plus_PrOrder _ _ v),(Q'_Plus_PrOrder _ _ u); auto with Q'.
        rewrite H12,Q'_Plus_Property,(Q'_Plus_Commutation v),
        <-Q'_Plus_Association,H11,Q'_Plus_Commutation,Q'_Plus_Property; auto. }
      rewrite H17. apply φn_is_Function_Lemma1; auto.
    + rewrite H8 in H7. apply (Q'_Ord_Trans v) in H7; auto.
      elim (Q'_Ord_irReflex v v); auto.
  - destruct H8 as [H8|[]].
    + rewrite H7 in H8. apply (Q'_Ord_Trans v) in H8; auto.
      elim (Q'_Ord_irReflex v v); auto.
    + assert (v ∈ \{ λ u, u ∈ Q'_Z /\ u < Q'0 \}).
      { apply AxiomII; split; eauto. }
      rewrite Q'_N_Neg_equ_Q'_Z_lt_Q'0 in H9; auto.
      apply AxiomII in H9 as [_[_[v0[]]]]. pose proof H9.
      apply MKT4' in H11 as [H11 _]. pose proof H11.
      apply Q'_N_propersubset_Q'_Arch,Q'_Arch_subset_Q' in H11; auto.
      apply Q'_N_Q'0_is_FirstMember in H9; auto.
      assert (u - v = v0 - Q'0).
      { apply Q'_Minus_Plus; auto with Q'. rewrite <-Q'_Mix_Association1,H10; auto.
        apply Q'_Minus_Plus; auto. rewrite <-H7,Q'_Plus_Property; auto. }
      rewrite H13. apply φn_is_Function_Lemma1; auto. apply Q'0_in_Q'_N; auto.
    + elim (Q'_Ord_irReflex v u); auto. rewrite <-H7,<-H8; auto.
Qed.

Close Scope q'_scope.

Lemma φz_is_Function_Lemma2 : ∀ u v, u ∈ Q'_Z -> v ∈ Q'_Z -> u <> v
  -> \[u\] <> \[v\].
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_Z_propersubset_Q'_Arch in H2;
  apply Q'_Z_propersubset_Q'_Arch in H3; auto.
  pose proof H; pose proof H0.
  apply Q'_Z_propersubset_Q'_Arch,Q'_Arch_subset_Q' in H4;
  apply Q'_Z_propersubset_Q'_Arch,Q'_Arch_subset_Q' in H5; auto.
  assert (Q'1 ∈ (Q'_N ~ [Q'0])).
  { pose proof Q'1_in_Q'_N. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. intro. pose proof Q'0_in_Q'.
    apply MKT41 in H7; eauto. elim Q'0_isnot_Q'1; auto. }
  assert (u ∈ Q' /\ v ∈ Q') as []; auto.
  apply (Q'_Ord_Tri u v) in H7 as [H7|[]];
  try contradiction; auto; clear H8; intro.
  - symmetry in H8. apply R_Q'_Property in H8; auto.
    apply AxiomII in H8 as [H8[]]. apply H10 in H6.
    rewrite Q'_Divide_Property2 in H6; auto with Q'. pose proof H7.
    apply φz_is_Function_Lemma1 in H11 as []; auto.
    + rewrite <-H11 in H6.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
    + apply (Q'_Ord_Trans Q'1) in H6; auto with Q'.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
  - apply R_Q'_Property in H8; auto.
    apply AxiomII in H8 as [H8[]]. apply H10 in H6.
    rewrite Q'_Divide_Property2 in H6; auto with Q'. pose proof H7.
    apply φz_is_Function_Lemma1 in H11 as []; auto.
    + rewrite <-H11 in H6.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
    + apply (Q'_Ord_Trans Q'1) in H6; auto with Q'.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
Qed.

(* φn是一一函数 定义域为 *Q_Z 值域是Z. *)
Property φz_is_Function : Function1_1 φz /\ dom(φz) = Q'_Z /\ ran(φz) = Ｚ.
Proof.
  intros. assert (Function1_1 φz).
  { repeat split; intros.
    - unfold Relation; intros.
      apply AxiomII in H as [H[u[v[]]]]; eauto.
    - apply AxiomII' in H as [H1[]];
      apply AxiomII' in H0 as [H0[]]. rewrite H2,H4; auto.
    - unfold Relation; intros.
      apply AxiomII in H as [H[u[v[]]]]; eauto.
    - apply AxiomII' in H as []; apply AxiomII' in H0 as [].
      apply AxiomII' in H1 as [H1[]]; apply AxiomII' in H2 as [H2[]].
      destruct (classic (y = z)); auto.
      apply φz_is_Function_Lemma2 in H7; auto.
      elim H7. rewrite <-H4,<-H6; auto. }
  split; auto. destruct H. split.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2; tauto.
    + apply AxiomII; split. eauto. exists (\[z\]). pose proof H1.
      apply Q'_Z_propersubset_Q'_Arch,(R_Instantiate2 z) in H2.
      apply AxiomII'; split; auto. apply MKT49a; eauto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2 as [H2[]].
      rewrite H4. apply AxiomII; split; eauto. rewrite <-H4; auto.
    + apply AxiomII; split. eauto. apply AxiomII in H1 as [H1[x[]]].
      exists x. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Property φz_Q'0 : φz[Q'0] = R0.
Proof.
  intros. destruct φz_is_Function as [[][]]. pose proof Q'0_in_Q'_Z.
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3 as [_[]]; auto.
Qed.

Property φz_Q'1 : φz[Q'1] = R1.
Proof.
  intros. destruct φz_is_Function as [[][]]. pose proof Q'1_in_Q'_Z.
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3 as [_[]]; auto.
Qed.

(* φz是序保持的. *)
Property φz_PrOrder : ∀ u v, u ∈ Q'_Z -> v ∈ Q'_Z
  -> (u < v)%q' <-> φz[u] < φz[v].
Proof.
  intros. destruct φz_is_Function as [[][]].
  assert (φz[u] = \[u\]).
  { rewrite <-H3 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φz[v] = \[v\]).
  { rewrite <-H3 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  pose proof H; pose proof H0.
  apply Q'_Z_propersubset_Q'_Arch in H7;
  apply Q'_Z_propersubset_Q'_Arch in H8; auto.
  pose proof H7; pose proof H8.
  apply Q'_Arch_subset_Q' in H9; apply Q'_Arch_subset_Q' in H10; auto.
  rewrite H5,H6. split; intros.
  - assert (u <> v).
    { intro. rewrite H12 in H11. elim (Q'_Ord_irReflex v v); auto. }
    apply Q'_Ord_to_R_Ord in H11 as []; auto.
    apply φz_is_Function_Lemma2 in H12; auto; try contradiction.
  - apply R_Ord_Instantiate in H11; tauto.
Qed.

(* φz是加法保持的. *)
Property φz_PrPlus : ∀ u v, u ∈ Q'_Z -> v ∈ Q'_Z
  -> φz[(u + v)%q'] = φz[u] + φz[v].
Proof.
  intros. pose proof H. apply (Q'_Z_Plus_in_Q'_Z u v) in H1; auto.
  destruct φz_is_Function as [[][]]. rewrite <-H4 in H1.
  apply Property_Value in H1; auto. apply AxiomII' in H1 as [H1[]].
  assert (φz[u] = \[u\]).
  { rewrite <-H4 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φz[v] = \[v\]).
  { rewrite <-H4 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  rewrite H7,H8,H9,R_Plus_Instantiate; try apply Q'_Z_propersubset_Q'_Arch; auto.
Qed.

(* φz是乘法保持的. *)
Corollary φz_PrMult : ∀ u v, u ∈ Q'_Z -> v ∈ Q'_Z
  -> φz[(u · v)%q'] = φz[u] · φz[v].
Proof.
  intros. pose proof H. apply (Q'_Z_Mult_in_Q'_Z u v) in H1; auto.
  destruct φz_is_Function as [[][]]. rewrite <-H4 in H1.
  apply Property_Value in H1; auto. apply AxiomII' in H1 as [H1[]].
  assert (φz[u] = \[u\]).
  { rewrite <-H4 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φz[v] = \[v\]).
  { rewrite <-H4 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  rewrite H7,H8,H9,R_Mult_Instantiate; try apply Q'_Z_propersubset_Q'_Arch; auto.
Qed.

Property R0_in_Z : R0 ∈ Ｚ.
Proof.
  pose proof R0_in_R. apply AxiomII; split; eauto. exists Q'0. split; auto.
  apply Q'_N_propersubset_Q'_Z,Q'0_in_Q'_N; auto.
Qed.

Global Hint Resolve R0_in_Z : R.

Property R1_in_Z : R1 ∈ Ｚ.
Proof.
  pose proof R1_in_R. apply AxiomII; split; eauto. exists Q'1. split; auto.
  apply Q'_N_propersubset_Q'_Z,Q'1_in_Q'_N; auto.
Qed.

Global Hint Resolve R1_in_Z : R.

(* Z对加法封闭. *)
Property Z_Plus_in_Z : ∀ u v, u ∈ Ｚ -> v ∈ Ｚ -> (u + v) ∈ Ｚ.
Proof.
  intros. pose proof H; pose proof H0.
  apply Z_propersubset_R in H1; apply Z_propersubset_R in H2; auto.
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H0 as [H0[y[]]].
  pose proof H1. apply (R_Plus_in_R u v) in H7; auto.
  apply AxiomII; split; eauto. exists (x + y)%q'. split.
  apply Q'_Z_Plus_in_Q'_Z; auto. rewrite H4,H6,R_Plus_Instantiate;
  try apply Q'_Z_propersubset_Q'_Arch; auto.
Qed.

Global Hint Resolve Z_Plus_in_Z : R.

(* Z对乘法封闭. *)
Property Z_Mult_in_Z : ∀ u v, u ∈ Ｚ -> v ∈ Ｚ -> (u · v) ∈ Ｚ.
Proof.
  intros. pose proof H; pose proof H0.
  apply Z_propersubset_R in H1; apply Z_propersubset_R in H2; auto.
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H0 as [H0[y[]]].
  pose proof H1. apply (R_Mult_in_R u v) in H7; auto.
  apply AxiomII; split; eauto. exists (x · y)%q'. split.
  apply Q'_Z_Mult_in_Q'_Z; auto. rewrite H4,H6,R_Mult_Instantiate;
  try apply Q'_Z_propersubset_Q'_Arch; auto.
Qed.

Global Hint Resolve Z_Mult_in_Z : R.

(* 减法在Z中封闭. *)
Property Z_Minus_in_Z : ∀ u v, u ∈ Ｚ -> v ∈ Ｚ -> (u - v) ∈ Ｚ.
Proof.
  intros. pose proof H; pose proof H0.
  apply AxiomII in H as [H[z1[]]]. apply AxiomII in H0 as [H0[z2[]]].
  pose proof H3. apply (Q'_Z_Minus_in_Q'_Z z1 z2) in H7; auto.
  set (z := (z1 - z2)%q').
  apply Z_propersubset_R in H1; apply Z_propersubset_R in H2; auto.
  assert (\[z\] ∈ Ｒ).
  { apply R_Instantiate2; auto. apply Q'_Z_propersubset_Q'_Arch; auto. }
  assert (u - v = \[z\]).
  { apply R_Minus_Plus; auto. unfold z.
    rewrite H4,H6,R_Plus_Instantiate,<-Q'_Mix_Association1,
    Q'_Plus_Commutation,Q'_Mix_Association1;
    try apply Q'_Z_subset_Q'; try apply Q'_Z_propersubset_Q'_Arch;
    auto. replace (z2 - z2)%q' with Q'0.
    rewrite Q'_Plus_Property; auto. apply Q'_Z_subset_Q'; auto.
    symmetry. apply Q'_Minus_Plus; try apply Q'_Z_subset_Q'; auto.
    apply Q'0_in_Q'_Z. apply Q'_Plus_Property,Q'_Z_subset_Q'; auto. }
  rewrite H9. apply AxiomII; split; eauto.
Qed.

Global Hint Resolve Z_Minus_in_Z : R.

(* N与Z的关系:
   N是Z中大于等于0的部分. 即, 自然数是非负整数 *)
Property N_equ_Z_me_R0 : Ｎ = \{ λ u, u ∈ Ｚ /\ (R0 = u \/ R0 < u) \}.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII; repeat split; eauto.
    + apply AxiomII in H as [H[x[]]].
      apply Q'_N_propersubset_Q'_Z in H0; auto.
      apply AxiomII; split; eauto.
    + pose proof R0_in_R. pose proof H. apply N_propersubset_R in H1; auto.
      assert (R0 ∈ Ｒ /\ z ∈ Ｒ) as []; auto.
      apply (R_Ord_Tri _ z) in H2 as [H2|[]]; auto; clear H3.
      pose proof H. apply AxiomII in H3 as [H3[x[]]].
      pose proof H4. apply Q'_N_propersubset_Q'_Arch in H6; auto.
      pose proof H6. apply Q'_Arch_subset_Q' in H7; auto.
      pose proof Q'0_in_Q'_Arch. rewrite H5 in H2.
      apply R_Ord_Instantiate in H2 as []; auto.
      destruct (classic (x = Q'0)).
      * rewrite <-H10 in H2. elim (Q'_Ord_irReflex x x); auto.
      * assert (x ∈ (Q'_N ~ [Q'0])).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto.
          intro. apply MKT41 in H11; eauto. }
        apply Q'_N_Q'0_is_FirstMember in H11; auto.
        apply (Q'_Ord_Trans x) in H11; auto.
        elim (Q'_Ord_irReflex x x); auto. apply Q'_Arch_subset_Q'; auto.
  - apply AxiomII in H as [H[]]. apply AxiomII in H0 as [H0[x[]]].
    apply AxiomII; split; auto. exists x. split; auto.
    rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; repeat split; eauto.
    pose proof H2. apply Q'_Z_propersubset_Q'_Arch in H4; auto.
    pose proof H4. apply Q'_Arch_subset_Q' in H5; auto. pose proof Q'0_in_Q'.
    assert (Q'0 ∈ Q' /\ x ∈ Q') as []; auto.
    apply (Q'_Ord_Tri _ x) in H7 as [H7|[]]; auto; clear H8. destruct H1.
    + rewrite H3 in H1. pose proof Q'0_in_Q'_Arch. apply R_Q'_Property in H1; auto.
      assert (x ∈ \{ λ u, u ∈ Q'_Z /\ u < Q'0 \})%q'.
      { apply AxiomII; split; eauto. }
      rewrite Q'_N_Neg_equ_Q'_Z_lt_Q'0 in H9; auto.
      apply AxiomII in H9 as [_[_[x0[]]]].
      pose proof H9. apply MKT4' in H11 as [H11 _].
      pose proof H11. apply Q'_N_propersubset_Q'_Arch in H12; auto.
      pose proof H12. apply Q'_Arch_subset_Q' in H13; auto.
      assert (Q'0 - x = x0)%q'. { apply Q'_Minus_Plus; auto. }
      rewrite H14 in H1. apply AxiomII in H1 as [_[_ H1]].
      apply Q'_N_Q'0_is_FirstMember in H9; auto.
      assert (|x0| = x0)%q'. { apply mt_Q'0_Q'Abs; auto. }
      assert (Q'1 ∈ (Q'_N ~ [Q'0])).
      { pose proof Q'1_in_Q'_N. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. intro. apply MKT41 in H17; eauto.
        elim Q'0_isnot_Q'1; auto. }
      apply H1 in H16. rewrite H15,Q'_Divide_Property2 in H16; auto with Q'.
      destruct φ4_is_Function as [[][]]. assert (x0 ∈ ran(φ4)); auto.
      rewrite reqdi in H21. apply Property_Value,Property_ran in H21; auto.
      rewrite <-deqri,H19 in H21. assert (x0 = φ4[(φ4⁻¹)[x0]]). rewrite f11vi; auto.
      rewrite H22,<-φ4_0 in H9; rewrite H22,<-φ4_1 in H16; auto.
      apply φ4_PrOrder in H9; apply φ4_PrOrder in H16;
      try apply in_ω_0; try apply in_ω_1; auto. pose proof in_ω_0.
      apply MKT41 in H16; eauto. rewrite H16 in H9. elim (@ MKT16 0); auto.
    + rewrite H3 in H1. apply R_Ord_Instantiate in H1 as []; auto.
      apply Q'0_in_Q'_Arch; auto.
Qed.

(* N与Z的关系:
   N的非零元的负元组成的集 是Z中小于0的部分. 即, 负整数是 非零自然数的负值 *)
Property N_Neg_equ_Z_lt_R0 : \{ λ u, u ∈ Ｚ /\ u < R0 \}
  = \{ λ u, u ∈ Ｒ /\ ∃ v, v ∈ (Ｎ ~ [R0]) /\ u + v = R0 \}.
Proof.
  Open Scope q'_scope.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]].
    apply AxiomII; repeat split; auto.
    apply Z_propersubset_R; auto. apply AxiomII in H0 as [_[x[]]].
    pose proof H0. apply Q'_Z_propersubset_Q'_Arch in H3; auto.
    pose proof H0. apply Q'_Z_subset_Q' in H4; auto.
    pose proof Q'0_in_Q'_Arch. pose proof Q'0_in_Q'. rewrite H2 in H1.
    apply R_Ord_Instantiate in H1 as [H1 _]; auto.
    assert (x ∈ \{ λ u, u ∈ Q'_Z /\ u < Q'0 \}). { apply AxiomII; split; eauto. }
    rewrite Q'_N_Neg_equ_Q'_Z_lt_Q'0 in H7; auto.
    apply AxiomII in H7 as [H7[H8[x0[]]]].
    apply MKT4' in H9 as []. pose proof H9.
    apply Q'_N_propersubset_Q'_Arch in H12; auto. exists (\[x0\])%r.
    assert (\[x0\] ∈ Ｒ)%r. { apply R_Instantiate2; auto. }
    split.
    + apply MKT4'; split. apply AxiomII; split; eauto.
      apply AxiomII; split; eauto. intro. pose proof R0_in_R.
      apply MKT41 in H14; eauto. apply R_Q'_Property in H14; auto.
      replace (x0 - Q'0) with x0 in H14. apply AxiomII in H14 as [_[]].
      assert (Q'1 ∈ (Q'_N ~ [Q'0])).
      { pose proof Q'1_in_Q'_N. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. intro. apply MKT41 in H18; eauto.
        elim Q'0_isnot_Q'1; auto. } apply H16 in H17.
      assert (Q'0 < x0).
      { apply (Q'_Plus_PrOrder _ _ x); auto. rewrite Q'_Plus_Property,H10; auto. }
      pose proof H18. apply mt_Q'0_Q'Abs in H19; auto.
      rewrite H19,Q'_Divide_Property2 in H17; auto with Q'.
      destruct φ4_is_Function as [[][]]. assert (x0 ∈ ran(φ4)); auto.
      rewrite reqdi in H24. apply Property_Value,Property_ran in H24; auto.
      rewrite <-deqri,H22 in H24.
      assert (x0 = φ4[(φ4⁻¹)[x0]]). { rewrite f11vi; auto. }
      rewrite <-φ4_0,H25 in H18; auto. rewrite <-φ4_1,H25 in H17; auto.
      apply φ4_PrOrder in H17; apply φ4_PrOrder in H18;
      try apply in_ω_0; try apply in_ω_1; auto.
      pose proof in_ω_0. apply MKT41 in H17; eauto.
      rewrite H17 in H18. elim (@ MKT16 0); auto. symmetry.
      apply Q'_Arch_subset_Q' in H12; auto. apply Q'_Minus_Plus; auto.
      rewrite Q'_Plus_Commutation, Q'_Plus_Property; auto.
    + rewrite H2,R_Plus_Instantiate,H10; auto.
  - apply AxiomII in H as [H[H0[z0[]]]]. apply MKT4' in H1 as [].
    pose proof H1. apply N_propersubset_R in H4; auto.
    pose proof H1. rewrite N_equ_Z_me_R0 in H5; auto.
    apply AxiomII in H5 as [_[]]. destruct H6. rewrite H6 in H3.
    apply AxiomII in H3 as []. elim H7. apply MKT41; eauto.
    apply AxiomII; repeat split; auto.
    + inR H0 x. apply AxiomII in H5 as [_[x0[]]]. rewrite H9 in H6.
      apply R_Ord_Instantiate in H6 as [H6 _]; try apply Q'0_in_Q'_Arch;
      try apply Q'_Z_propersubset_Q'_Arch; auto. pose proof H5.
      apply Q'_Z_subset_Q' in H10; auto. pose proof H10.
      apply Q'_Neg in H11 as [xf[[]_]]; auto.
      assert (xf ∈ \{ λ u, u ∈ Q'_Z /\ u < Q'0 \}).
      { rewrite Q'_N_Neg_equ_Q'_Z_lt_Q'0; auto.
        apply AxiomII; repeat split; eauto. exists x0.
        rewrite Q'_Plus_Commutation in H12; auto. split; auto.
        apply MKT4'; split. rewrite Q'_N_equ_Q'_Z_me_Q'0; auto.
        apply AxiomII; split; eauto. apply AxiomII; split; eauto.
        intro. pose proof Q'0_in_Q'. apply MKT41 in H13; eauto.
        rewrite <-H13 in H6. elim (Q'_Ord_irReflex x0 x0); auto. }
      apply AxiomII in H13 as [H13[]]. apply AxiomII; split; auto.
      exists xf. split; auto. rewrite H8,H9,R_Plus_Instantiate in H2; auto;
      try apply Q'_Z_propersubset_Q'_Arch; auto. rewrite H8.
      apply R_Q'_Property; auto; try apply Q'_Z_propersubset_Q'_Arch; auto.
      pose proof H5. apply Q'_Z_propersubset_Q'_Arch in H16; auto.
      apply R_Q'_Property in H2; auto with Q'.
      replace (x - xf) with ((x + x0) - Q'0); auto.
      apply Q'_Minus_Plus; auto with Q'.
      rewrite Q'_Plus_Commutation,Q'_Plus_Property; auto with Q'.
      apply Q'_Minus_Plus; auto with Q'.
      rewrite (Q'_Plus_Commutation x),<-Q'_Plus_Association,
      (Q'_Plus_Commutation xf),H12,Q'_Plus_Commutation,
      Q'_Plus_Property; auto with Q'.
    + apply (R_Plus_PrOrder _ _ z) in H6; try apply R0_in_R; auto.
      rewrite R_Plus_Property,H2 in H6; auto.
  Close Scope q'_scope.
Qed.

(* 根据以上分析立得: N 是 Z 的真子集. *)
Property N_propersubset_Z : Ｎ ⊂ Ｚ /\ Ｎ <> Ｚ.
Proof.
  split.
  - unfold Included; intros. rewrite N_equ_Z_me_R0 in H; auto.
    apply AxiomII in H; tauto.
  - intro. pose proof R1_in_R. pose proof R0_in_R.
    assert (R0 < R1).
    { apply R_Ord_Instantiate; auto with Q'. split.
      apply Q'0_lt_Q'1; auto. intro. symmetry in H2.
      apply R_Q'_Property in H2; auto with Q'.
      pose proof Q'0_lt_Q'1. replace (Q'1 - Q'0)%q' with Q'1 in H2.
      apply AxiomII in H2 as [H2[]]. pose proof Q'0_in_Q'.
      assert (Q'1 ∈ (Q'_N ~ [Q'0])).
      { pose proof Q'1_in_Q'_N. apply MKT4'; split; auto.
        apply AxiomII; split; auto. intro. apply MKT41 in H8; eauto.
        elim Q'0_isnot_Q'1; auto. }
      apply H5 in H7. apply mt_Q'0_Q'Abs in H3; auto.
      rewrite H3,Q'_Divide_Property2 in H7; auto.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto.
      rewrite Q'_Minus_Property2; auto with Q'. }
    pose proof H0. apply R_Neg_Property in H3 as [a[[]_]]; auto.
    assert (a ∈ \{ λ u, u ∈ Ｒ /\ ∃ v, v ∈ (Ｎ ~ [R0]) /\ u + v = R0 \}).
    { apply AxiomII; repeat split; eauto. exists R1. split.
      pose proof R1_in_N. apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H6; eauto. elim R0_isnot_R1; auto.
      rewrite R_Plus_Commutation; auto. }
    rewrite <-N_Neg_equ_Z_lt_R0 in H5; auto.
    apply AxiomII in H5 as [_ []]. rewrite <-H in H5.
    rewrite N_equ_Z_me_R0 in H5; auto.
    apply AxiomII in H5 as [_ [H5[]]].
    + rewrite H7 in H6. elim (R_Ord_irReflex a a); auto.
    + apply (R_Ord_Trans a) in H7; auto. elim (R_Ord_irReflex a a); auto.
Qed.
(* 至此,  *Q_Z 和 Z 是同构的, 选取其中任意一个都可以作为整数集使用.  *)

(* R中的Q由*Q_Q中元的等价类组成. *)
Definition Ｑ := \{ λ u, ∃ q, q ∈ Q'_Q /\ u = \[q\] \}.

Property Q_is_Set : Ensemble Ｑ.
Proof.
  apply (MKT33 Ｒ). apply R_is_Set; auto. unfold Included; intros.
  apply AxiomII in H as [H[x[]]]. rewrite H1. apply R_Instantiate2; auto.
  apply Q'_Q_subset_Q'_Arch; auto.
Qed.

(* 有理数集是实数集的子集 (关于真子集的讨论放在之后) *)
Property Q_subset_R : Ｑ ⊂ Ｒ.
Proof.
  unfold Included; intros. apply AxiomII in H as [H[x[]]].
  rewrite H1. apply R_Instantiate2; auto. apply Q'_Q_subset_Q'_Arch; auto.
Qed.

(* 定义一个函数: 以证明 *Q_Q 与 Q 同构 *)
Definition φq := \{\ λ u v, u ∈ Q'_Q /\ v = \[u\] \}\.

(* 以下两个引理为证明φq是一一函数做准备. *)
(* *Q_Q对元素的逆元封闭. *)
Lemma φq_is_Function_Lemma1 : ∀ u, u ∈ Q'_Q -> u <> Q'0
   -> ∃! v, v ∈ Q'_Q /\ v <> Q'0 /\ (u · v)%q' = Q'1.
Proof.
  intros. pose proof H. apply Q'_Q_subset_Q' in H1; auto.
  pose proof H. apply AxiomII in H2 as [H2[x[y[H3[]]]]].
  Z'split1 H4 H6. pose proof H4. apply MKT4' in H9 as [H9 _].
  pose proof Z'0_in_Z'.
  assert (x ∈ (Z'_Z ~ [Z'0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
    apply MKT41 in H11; eauto. elim H0. rewrite H5,Q'0_Property,H11; auto.
    apply R_Z'_Property; auto with Z'.
    rewrite Z'_Mult_Property2,Z'_Mult_Property1; auto. }
  Z'split1 H11 H12. pose proof H11. apply MKT4' in H15 as [H15 _].
  set (u1 := (\[[y,x]\])%q').
  assert (u1 ∈ Q'). { apply Q'_Instantiate2; auto. }
  assert (u1 ∈ Q'_Q). { apply AxiomII; split; eauto. }
  assert (u1 <> Q'0).
  { intro. unfold u1 in H18. rewrite Q'0_Property in H18; auto.
    apply R_Z'_Property in H18; auto with Z'.
    rewrite Z'_Mult_Property2,Z'_Mult_Property1 in H18; auto. }
  assert (u · u1 = Q'1)%q'.
  { unfold u1. rewrite H5,Q'_Mult_Instantiate,Q'1_Property,
    Z'_Mult_Commutation; auto. apply R_Z'_Property; auto with Z'. }
  exists u1. repeat split; auto. intros w [H20[]].
  rewrite <-H19 in H22. apply Q'_Mult_Cancellation in H22; auto.
  apply Q'_Q_subset_Q'; auto.
Qed.

(* 对于Q中的元素 [a]和[b] 若a<>b则[a]<>[b]. *)
Lemma φq_is_Function_Lemma2 : ∀ a b, a ∈ Q'_Q -> b ∈ Q'_Q -> a <> b
  -> \[a\] <> \[b\].
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_Q_subset_Q'_Arch in H2; apply Q'_Q_subset_Q'_Arch in H3; auto.
  intro. apply R_Q'_Property in H4; auto. pose proof H2; pose proof H3.
  apply Q'_Arch_subset_Q' in H5; apply Q'_Arch_subset_Q' in H6; auto.
  pose proof Q'0_in_Q'. assert (a - b <> Q'0)%q'.
  { intro. apply Q'_Minus_Plus in H8; auto.
    rewrite Q'_Plus_Property in H8; auto. }
  assert ((a - b) ∈ (I ~ [Q'0]))%q'.
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H9; eauto. }
  assert ((a - b) ∈ Q'_Q)%q'. { apply Q'_Q_Minus_in_Q'_Q; auto. }
  pose proof H10. apply φq_is_Function_Lemma1 in H11 as [v[[H11[]]_]]; auto.
  destruct NPAUF as [_]. apply I_Inv_Property1 in H13; auto;
  try apply Q'_Q_subset_Q'; auto. apply Q'_Q_subset_Q'_Arch in H11; auto.
  apply MKT4' in H13 as []. apply AxiomII in H15 as []; auto.
Qed.

(* φq是一一函数 定义域为 *Q_Q 值域是Q. *)
Property φq_is_Function : Function1_1 φq /\ dom(φq) = Q'_Q /\ ran(φq) = Ｑ.
Proof.
  assert (Function1_1 φq).
  { repeat split; intros.
    - unfold Relation; intros. apply AxiomII in H as [H[u[v[]]]]; eauto.
    - apply AxiomII' in H as [H1[]];
      apply AxiomII' in H0 as [H0[]]. rewrite H2,H4; auto.
    - unfold Relation; intros. apply AxiomII in H as [H[u[v[]]]]; eauto.
    - apply AxiomII' in H as []; apply AxiomII' in H0 as [].
      apply AxiomII' in H1 as [H1[]]; apply AxiomII' in H2 as [H2[]].
      destruct (classic (y = z)); auto. apply φq_is_Function_Lemma2 in H7; auto.
      elim H7. rewrite <-H4,<-H6; auto. }
  split; auto. destruct H. split.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2; tauto.
    + apply AxiomII; split. eauto. exists (\[z\]). pose proof H1.
      apply Q'_Q_subset_Q'_Arch,(R_Instantiate2 z) in H2.
      apply AxiomII'; split; auto. apply MKT49a; eauto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2 as [H2[]].
      rewrite H4. apply AxiomII; split; eauto. rewrite <-H4; auto.
    + apply AxiomII; split. eauto. apply AxiomII in H1 as [H1[x[]]].
      exists x. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Property φq_Q'0 : φq[Q'0] = R0.
Proof.
  destruct φq_is_Function as [[][]]. pose proof Q'0_in_Q'_Q.
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3 as [_[]]; auto.
Qed.

Property φq_Q'1 : φq[Q'1] = R1.
Proof.
  destruct φq_is_Function as [[][]]. pose proof Q'1_in_Q'_Q.
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3 as [_[]]; auto.
Qed.

(* φq是序保持的. *)
Property φq_PrOrder : ∀ u v, u ∈ Q'_Q -> v ∈ Q'_Q
  -> (u < v)%q' <-> φq[u] < φq[v].
Proof.
  intros. destruct φq_is_Function as [[][]].
  assert (φq[u] = \[u\]).
  { rewrite <-H3 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φq[v] = \[v\]).
  { rewrite <-H3 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  pose proof H; pose proof H0.
  apply Q'_Q_subset_Q'_Arch in H7; apply Q'_Q_subset_Q'_Arch in H8; auto.
  pose proof H7; pose proof H8.
  apply Q'_Arch_subset_Q' in H9; apply Q'_Arch_subset_Q' in H10; auto.
  rewrite H5,H6. split; intros.
  - assert (u <> v).
    { intro. rewrite H12 in H11. elim (Q'_Ord_irReflex v v); auto. }
    apply Q'_Ord_to_R_Ord in H11 as []; auto.
    apply φq_is_Function_Lemma2 in H12; auto; try contradiction.
  - apply R_Ord_Instantiate in H11; tauto.
Qed.

(* φq是加法保持的. *)
Property φq_PrPlus : ∀ u v, u ∈ Q'_Q -> v ∈ Q'_Q
  -> φq[(u + v)%q'] = φq[u] + φq[v].
Proof.
  intros. pose proof H. apply (Q'_Q_Plus_in_Q'_Q u v) in H1; auto.
  destruct φq_is_Function as [[][]]. rewrite <-H4 in H1.
  apply Property_Value in H1; auto. apply AxiomII' in H1 as [H1[]].
  assert (φq[u] = \[u\]).
  { rewrite <-H4 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φq[v] = \[v\]).
  { rewrite <-H4 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  rewrite H7,H8,H9,R_Plus_Instantiate; try apply Q'_Q_subset_Q'_Arch; auto.
Qed.

(* φq是乘法保持的. *)
Property φq_PrMult : ∀ u v, u ∈ Q'_Q -> v ∈ Q'_Q
  -> φq[(u · v)%q'] = φq[u] · φq[v].
Proof.
  intros. pose proof H. apply (Q'_Q_Mult_in_Q'_Q u v) in H1; auto.
  destruct φq_is_Function as [[][]]. rewrite <-H4 in H1.
  apply Property_Value in H1; auto. apply AxiomII' in H1 as [H1[]].
  assert (φq[u] = \[u\]).
  { rewrite <-H4 in H. apply Property_Value in H; auto.
    apply AxiomII' in H; tauto. }
  assert (φq[v] = \[v\]).
  { rewrite <-H4 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0; tauto. }
  rewrite H7,H8,H9,R_Mult_Instantiate; try apply Q'_Q_subset_Q'_Arch; auto.
Qed.
(* φq保证了 *Q_Q 与 Q 的同构性, 二者之一均可以作为有理数集使用. *)

Property R0_in_Q : R0 ∈ Ｑ.
Proof.
  pose proof R0_in_R. apply AxiomII; split; eauto. exists Q'0. split; auto.
  apply Q'_Z_propersubset_Q'_Q,Q'_N_propersubset_Q'_Z,Q'0_in_Q'_N; auto.
Qed.

Global Hint Resolve R0_in_Q : R.

Property R1_in_Q : R1 ∈ Ｑ.
Proof.
  pose proof R1_in_R. apply AxiomII; split; eauto. exists Q'1. split; auto.
  apply Q'_Z_propersubset_Q'_Q,Q'_N_propersubset_Q'_Z,Q'1_in_Q'_N; auto.
Qed.

Global Hint Resolve R1_in_Q : R.

(* Q对加法封闭. *)
Property Q_Plus_in_Q : ∀ u v, u ∈ Ｑ -> v ∈ Ｑ -> (u + v) ∈ Ｑ.
Proof.
  intros. pose proof H; pose proof H0.
  apply Q_subset_R in H1; apply Q_subset_R in H2; auto.
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H0 as [H0[y[]]].
  pose proof H1. apply (R_Plus_in_R u v) in H7; auto.
  apply AxiomII; split; eauto. exists (x + y)%q'.
  split. apply Q'_Q_Plus_in_Q'_Q; auto.
  rewrite H4,H6,R_Plus_Instantiate; try apply Q'_Q_subset_Q'_Arch; auto.
Qed.

Global Hint Resolve Q_Plus_in_Q : R.

(* Q对乘法封闭. *)
Property Q_Mult_in_Q : ∀ u v, u ∈ Ｑ -> v ∈ Ｑ -> (u · v) ∈ Ｑ.
Proof.
  intros. pose proof H; pose proof H0.
  apply Q_subset_R in H1; apply Q_subset_R in H2; auto.
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H0 as [H0[y[]]].
  pose proof H1. apply (R_Mult_in_R u v) in H7; auto.
  apply AxiomII; split; eauto. exists (x · y)%q'.
  split. apply Q'_Q_Mult_in_Q'_Q; auto.
  rewrite H4,H6,R_Mult_Instantiate; try apply Q'_Q_subset_Q'_Arch; auto.
Qed.

Global Hint Resolve Q_Mult_in_Q : R.

(* 减法在Q中封闭. *)
Property Q_Minus_in_Q : ∀ v u, v ∈ Ｑ -> u ∈ Ｑ -> (v - u) ∈ Ｑ.
Proof.
  intros. pose proof H; pose proof H0.
  apply AxiomII in H as [H[q1[]]]. apply AxiomII in H0 as [H0[q2[]]].
  pose proof H3. apply (Q'_Q_Minus_in_Q'_Q q1 q2) in H7; auto.
  set (q := (q1 - q2)%q'). apply Q_subset_R in H1; apply Q_subset_R in H2; auto.
  assert (\[q\] ∈ Ｒ).
  { apply R_Instantiate2; auto. apply Q'_Q_subset_Q'_Arch; auto. }
  assert (v - u = \[q\]).
  { apply R_Minus_Plus; auto. unfold q.
    rewrite H4,H6,R_Plus_Instantiate,<-Q'_Mix_Association1,
    Q'_Plus_Commutation,Q'_Mix_Association1;
    try apply Q'_Q_subset_Q'; try apply Q'_Q_subset_Q'_Arch; auto.
    replace (q2 - q2)%q' with Q'0.
    rewrite Q'_Plus_Property; auto. apply Q'_Q_subset_Q'; auto.
    symmetry. apply Q'_Minus_Plus;
    try apply Q'_Q_subset_Q'; auto. pose proof Q'0_in_Q'_N.
    apply Q'_N_propersubset_Q'_Z,Q'_Z_propersubset_Q'_Q in H9; auto.
    apply Q'_Plus_Property,Q'_Q_subset_Q'; auto. }
  rewrite H9. apply AxiomII; split; eauto.
Qed.

Global Hint Resolve Q_Minus_in_Q : R.

(* Q对除法封闭. *)
Property Q_Divide_in_Q : ∀ u v, u ∈ Ｑ -> v ∈ Ｑ -> v <> R0
  -> (u / v) ∈ Ｑ.
Proof.
  intros. pose proof H; pose proof H0. apply Q_subset_R in H,H0; auto.
  pose proof H1. apply R_Inv in H4 as [v1[[H4[]]_]]; auto.
  replace (u / v) with (u · v1).
  - apply Q_Mult_in_Q; auto. apply AxiomII; split; eauto.
    apply AxiomII in H3 as [_[y[]]]. pose proof H3.
    apply Q'_Q_subset_Q'_Arch in H8; auto. pose proof H4. inR H9 z.
    rewrite H7,H11,R_Mult_Instantiate in H6; auto.
    apply R_Q'_Property in H6; auto with Q'.
    destruct (classic (y = Q'0)).
    + elim H1. rewrite H7,H12; auto.
    + pose proof H3. apply Q'_Q_subset_Q' in H13; auto.
      pose proof H12. apply Q'_Inv in H14 as [y1[[H14[]]_]]; auto.
      rewrite <-H16,<-Q'_Mult_Distribution_Minus in H6; auto.
      apply I_Mult_in_I_Corollary in H6 as []; auto with Q'.
      * elim H1. rewrite H7; auto. apply R_Q'_Property; auto with Q'.
        rewrite Q'_Minus_Property2; auto.
      * exists y1. split. apply Q'_Divide_Mult in H16; auto with Q'.
        rewrite <-H16. apply Q'_Q_Divide_in_Q'_Q; auto.
        apply Q'1_in_Q'_Q; auto. rewrite H11. apply R_Q'_Property; auto.
        apply NNPP; intro.
        assert (y1 ∈ (Q' ~ Q'_Arch)).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
        rewrite Q'_Mult_Commutation in H16; auto. destruct NPAUF as [_].
        apply I_inv_Property2 in H16; auto. elim H1.
        apply MKT4' in H16 as []. rewrite H7; auto.
        apply R_Q'_Property; auto with Q'. rewrite Q'_Minus_Property2; auto.
  - symmetry. apply R_Divide_Mult; auto with R.
    rewrite (R_Mult_Commutation u),<-R_Mult_Association,H6,
    R_Mult_Commutation,R_Mult_Property2; auto with R.
Qed.

Global Hint Resolve Q_Divide_in_Q : R.

Open Scope q'_scope.

(* 引理：*Q_Z中的非零元的绝对值大于等于1 *)
Lemma Q_equ_Z_Div_Lemma : ∀ u, u ∈ (Q'_Z ~ [Q'0])
  -> Q'1 = |u| \/ Q'1 < |u|.
Proof.
  intros. apply MKT4' in H as []. pose proof Q'0_in_Q'_N.
  apply Q'_N_propersubset_Q'_Z in H1; auto. pose proof H; pose proof H1.
  apply Q'_Z_subset_Q' in H2; apply Q'_Z_subset_Q' in H3; auto.
  assert (Q'0 ∈ Q' /\ u ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ u) in H4 as [H4|[]]; auto; clear H5.
  - assert (u = u - Q'0).
    { symmetry. apply Q'_Minus_Plus; auto.
      rewrite Q'_Plus_Commutation,Q'_Plus_Property; auto. }
    rewrite H5. apply φz_is_Function_Lemma1; auto.
  - pose proof H4. apply lt_Q'0_Q'Abs in H5; auto.
    apply φz_is_Function_Lemma1 in H4; auto. rewrite <-H5 in H4.
    assert (|(|u|)| = |u|).
    { apply Q'0_le_Q'Abs in H2 as [H2[]]; auto.
      - rewrite H6. apply eq_Q'0_Q'Abs; auto.
      - apply mt_Q'0_Q'Abs in H6; auto. }
    rewrite H6 in H4; auto.
  - rewrite H4 in H0. apply AxiomII in H0 as []. elim H5. apply MKT41; auto.
Qed.

Close Scope q'_scope.

(* Q与Z的关系:
   Q是Z中的元素做除法而来. *)
Property Q_equ_Z_Div : Ｑ = \{ λ u, u ∈ Ｒ
  /\ ∃ a b, a ∈ Ｚ /\ b ∈ (Ｚ ~ [R0]) /\ u = a / b \}.
Proof.
  Open Scope q'_scope.
  intros. apply AxiomI; split; intros.
  - apply AxiomII; repeat split; eauto. apply Q_subset_R; auto.
    apply AxiomII in H as [H[q[]]]. pose proof H0 as H0a. 
    apply Q'_Q_subset_Q'_Arch in H0a; auto.
    pose proof H0a as H0b. apply Q'_Arch_subset_Q' in H0b; auto.
    apply AxiomII in H0 as [H0[x[y[H2[]]]]]. pose proof H2.
    apply Z'_Z_subset_Z' in H5; auto. Z'split1 H3 H6.
    pose proof H3. apply MKT4' in H9 as [H9 _].
    set (a := \[[x,Z'1]\]). set (b := \[[y,Z'1]\]).
    assert (a ∈ Q'). { apply Q'_Instantiate2; auto with Z'. }
    assert (b ∈ Q'). { apply Q'_Instantiate2; auto with Z'. }
    assert (a ∈ Q'_Z /\ b ∈ Q'_Z) as [].
    { split; auto; apply AxiomII; split; eauto. }
    assert (b ∈ (Q'_Z ~ [Q'0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
      pose proof Q'0_in_Q'. apply MKT41 in H14; eauto. unfold b in H14.
      rewrite Q'0_Property in H14; auto.
      apply R_Z'_Property in H14; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Property1 in H14; auto with Z'. }
    pose proof H12; pose proof H13.
    apply Q'_Z_propersubset_Q'_Arch in H15;
    apply Q'_Z_propersubset_Q'_Arch in H16; auto.
    set (ra := (\[a\])%r). set (rb := (\[b\])%r).
    assert (ra ∈ Ｒ). { apply R_Instantiate2; auto. }
    assert (rb ∈ Ｒ). { apply R_Instantiate2; auto. }
    assert (ra ∈ Ｚ). { apply AxiomII; split; eauto. }
    assert (rb ∈ Ｚ). { apply AxiomII; split; eauto. }
    assert (rb ∈ (Ｚ ~ [R0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
      pose proof R0_in_R. apply MKT41 in H21; eauto. unfold rb,R0 in H21.
      apply R_Q'_Property in H21; auto with Q'.
      assert (b - Q'0 = b).
      { apply Q'_Minus_Plus; auto with Q'.
        rewrite Q'_Plus_Commutation,Q'_Plus_Property; auto with Q'. }
      rewrite H23 in H21. apply AxiomII in H21 as [_[]].
      assert (Q'1 ∈ (Q'_N ~ [Q'0])).
      { pose proof Q'1_in_Q'_N. pose proof Q'0_in_Q'_N. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. intro. apply MKT41 in H27; eauto.
        elim Q'0_isnot_Q'1; auto. }
      apply H24 in H25. rewrite Q'_Divide_Property2 in H25; auto with Q'.
      apply Q_equ_Z_Div_Lemma in H14 as []; auto.
      - rewrite <-H14 in H25. elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
      - apply (Q'_Ord_Trans Q'1) in H25; auto with Q'.
        elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'. }
    exists ra,rb. repeat split; auto. unfold ra,rb.
    symmetry. apply R_Divide_Mult; auto. intro.
    apply MKT4' in H21 as []. apply AxiomII in H23 as [].
    elim H24. apply MKT41; eauto with R. rewrite H1.
    apply R_Instantiate2; auto. rewrite H1,R_Mult_Instantiate; auto.
    symmetry. apply R_Q'_Property; auto with Q'.
    assert (a - (b · q) = Q'0).
    { apply Q'_Minus_Plus; auto with Q'.
      rewrite Q'_Plus_Property; auto with Q'. unfold a,b.
      rewrite H4,Q'_Mult_Instantiate; auto with Z'.
      apply R_Z'_Property; auto with Z'.
      rewrite Z'_Mult_Property2,(Z'_Mult_Commutation _ y),
      Z'_Mult_Property2; auto with Z'. }
    rewrite H22. pose proof Q'0_in_Q'. apply AxiomII; repeat split; eauto. intros.
    replace (|Q'0|) with Q'0. pose proof H24. apply MKT4' in H24 as [].
    apply Q'_N_subset_Q' in H24; auto. apply Q'_N_Q'0_is_FirstMember in H25; auto.
    assert (k <> Q'0).
    { intro. apply AxiomII in H26 as []. elim H28. apply MKT41; eauto. }
    apply (Q'_Mult_PrOrder _ _ k); auto with Q'.
    rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto with Q'.
    symmetry. apply eq_Q'0_Q'Abs; auto.
  - apply AxiomII in H as [H[H0[a[b[H1[]]]]]].
    pose proof H1. apply Z_propersubset_R in H4; auto.
    pose proof H0. inR H5 q. apply AxiomII in H1 as [H1[x[]]].
    apply MKT4' in H2 as []. pose proof H2. apply Z_propersubset_R in H11; auto.
    apply AxiomII in H2 as [H2[y[]]]. pose proof H8; pose proof H12.
    apply Q'_Z_propersubset_Q'_Arch in H14,H15; auto.
    pose proof H8; pose proof H12. apply AxiomII in H16 as [H16[x0[]]].
    apply AxiomII in H17 as [H17[y0[]]]. set (z0 := \[[x0,y0]\]).
    pose proof H18; pose proof H20. apply Z'_Z_subset_Z' in H22,H23; auto.
    assert (y0 ∈ (Z' ~ [Z'0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
      pose proof Z'0_in_Z'. apply MKT41 in H24; eauto. apply AxiomII in H10 as [].
      elim H26. pose proof R0_in_R. apply MKT41; eauto.
      rewrite H13,H21,H24,<-Q'0_Property; auto. }
    assert (z0 ∈ Q'). { apply Q'_Instantiate2; auto. }
    assert (z0 ∈ Q'_Q).
    { apply AxiomII; split; eauto. exists x0,y0. repeat split; auto.
      apply MKT4' in H24 as []. apply MKT4'; auto. }
    pose proof H26. apply Q'_Q_subset_Q'_Arch in H27; auto.
    set (w := (\[z0\])%r). assert (a = b · w)%r.
    { unfold w. rewrite H9,H13,R_Mult_Instantiate; auto.
      assert (x = y · z0).
      { unfold z0. rewrite H19,H21,Q'_Mult_Instantiate,
        (Z'_Mult_Commutation _ y0),Z'_Mult_Property2; auto with Z'.
        apply R_Z'_Property; auto with Z'.
        rewrite (Z'_Mult_Commutation Z'1),
        Z'_Mult_Property2,Z'_Mult_Commutation; auto with Z'. }
      rewrite H28; auto. }
    assert (w ∈ Ｒ). { apply R_Instantiate2; auto. }
    assert (w ∈ Ｑ). { apply AxiomII; split; eauto. }
    symmetry in H28. apply R_Divide_Mult in H28; auto.
    rewrite H3,H28; auto. intro. apply AxiomII in H10 as [].
    elim H33. apply MKT41; eauto with R.
  Close Scope q'_scope.
Qed.

(* 两个Z中的元素相除其结果在Q中. *)
Property Z_Divide_in_Q : ∀ v u, v ∈ Ｚ -> u ∈ Ｚ -> u <> R0
  -> (v / u) ∈ Ｑ.
Proof.
  intros. pose proof H. pose proof H0.
  apply Z_propersubset_R in H2,H3; auto.
  rewrite Q_equ_Z_Div; auto. apply AxiomII; repeat split; eauto with R.
  exists v,u. repeat split; auto. apply MKT4'; split; auto.
  apply AxiomII; split; eauto. intro. apply MKT41 in H4; eauto with R.
Qed.

(* Z 是 Q 的真子集. *)
Property Z_propersubset_Q : Ｚ ⊂ Ｑ /\ Ｚ <> Ｑ.
Proof.
  Open Scope q'_scope.
  split.
  - unfold Included; intros. apply AxiomII in H as [H[x[]]].
    apply Q'_Z_propersubset_Q'_Q in H0; auto. apply AxiomII; split; eauto.
  - intro. pose proof Q'1_in_Q'_N. apply Q'_N_propersubset_Q'_Z in H0; auto.
    pose proof H0. apply Q'_Z_propersubset_Q'_Arch in H1; auto.
    pose proof H1. apply Q'_Arch_subset_Q' in H2; auto.
    set (two := Q'1 + Q'1).
    assert (two ∈ Q'_Z). { apply Q'_Z_Plus_in_Q'_Z; auto. }
    pose proof H3. apply Q'_Z_propersubset_Q'_Arch in H4; auto.
    pose proof H4. apply Q'_Arch_subset_Q' in H5; auto. pose proof Q'0_in_Q'.
    assert (two <> Q'0).
    { pose proof Q'0_lt_Q'1. pose proof H7.
      apply (Q'_Plus_PrOrder _ _ Q'1) in H8; auto.
      rewrite Q'_Plus_Property in H8; auto.
      apply (Q'_Ord_Trans Q'0) in H8; auto. intro.
      unfold two in H9. rewrite H9 in H8.
      elim (Q'_Ord_irReflex Q'0 Q'0); auto. }
    pose proof H3. apply Q'_Z_propersubset_Q'_Q in H8; auto.
    pose proof H8. apply φq_is_Function_Lemma1 in H9 as [dw[[H9[]]_]]; auto.
    pose proof H9. apply Q'_Q_subset_Q'_Arch in H12; auto.
    pose proof H12. apply Q'_Arch_subset_Q' in H13; auto.
    set (rdw := (\[dw\])%r).
    assert (rdw ∈ Ｒ). { apply R_Instantiate2; auto. }
    assert (rdw ∈ Ｑ). { apply AxiomII; split; eauto. }
    rewrite <-H in H15. apply AxiomII in H15 as [H15[x[]]].
    pose proof H16. apply Q'_Z_propersubset_Q'_Arch in H18; auto.
    pose proof H18. apply Q'_Arch_subset_Q' in H19; auto.
    symmetry in H17. apply R_Q'_Property in H17; auto.
    assert (two · (x - dw) ∈ I).
    { rewrite Q'_Mult_Commutation; auto with Q'. }
    rewrite Q'_Mult_Distribution_Minus,H11 in H20; auto.
    remember (two · x) as m.
    assert (m ∈ Q'_Z).
    { rewrite Heqm. apply Q'_Z_Mult_in_Q'_Z; auto. }
    pose proof H21. apply Q'_Z_propersubset_Q'_Q in H22; auto.
    pose proof H22. apply Q'_Q_subset_Q'_Arch in H23; auto.
    pose proof H23. apply Q'_Arch_subset_Q' in H24; auto.
    apply AxiomII in H20 as [H20[]].
    assert (Q'1 ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split. apply Q'1_in_Q'_N; auto.
      apply AxiomII; split; eauto. intro.
      apply MKT41 in H27; eauto. elim Q'0_isnot_Q'1; auto. }
    apply H26 in H27. rewrite Q'_Divide_Property2 in H27; auto with Q'.
    assert (m ∈ Q' /\ Q'1 ∈ Q') as []; auto.
    apply (Q'_Ord_Tri m Q'1) in H28 as [H28|[]]; auto; clear H29.
    + assert (|(m - Q'1)| = |(Q'1 - m)|).
      { apply Neg_Q'Abs_Equ; auto with Q'.
        rewrite <-Q'_Mix_Association1,Q'_Plus_Commutation,
        <-Q'_Mix_Association1,(Q'_Plus_Commutation _ m),Q'_Mix_Association1; auto.
        rewrite Q'_Minus_Property1,Q'_Plus_Property,
        Q'_Minus_Property1; auto. }
      rewrite H29 in H27. apply φz_is_Function_Lemma1 in H28 as []; auto.
      rewrite <-H28 in H27. elim (Q'_Ord_irReflex Q'1 Q'1); auto.
      apply (Q'_Ord_Trans Q'1) in H27; auto with Q'.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto.
    + apply φz_is_Function_Lemma1 in H28 as []; auto. rewrite <-H28 in H27.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto.
      apply (Q'_Ord_Trans Q'1) in H27; auto with Q'.
      elim (Q'_Ord_irReflex Q'1 Q'1); auto.
    + rewrite Heqm,<-H11 in H28. apply Q'_Mult_Cancellation in H28; auto.
      assert (Q'1 < two).
      { pose proof Q'0_lt_Q'1. apply (Q'_Plus_PrOrder _ _ Q'1) in H29; auto.
        rewrite Q'_Plus_Property in H29; auto. }
      pose proof H29. apply (Q'_Ord_Trans Q'0) in H30; auto with Q'.
      assert (Q'0 < dw).
      { apply (Q'_Mult_PrOrder _ _ two); auto.
        rewrite H11,Q'_Mult_Property1; auto. apply Q'0_lt_Q'1; auto. }
      assert (dw < Q'1).
      { apply (Q'_Mult_PrOrder _ _ dw) in H29; auto.
        rewrite Q'_Mult_Property2,Q'_Mult_Commutation,H11 in H29; auto. }
      assert (x ∈ Q' /\ Q'0 ∈ Q') as []; auto.
      apply (Q'_Ord_Tri x Q'0) in H33 as [H33|[]]; auto; clear H34.
      * rewrite H28 in H33. apply (Q'_Ord_Trans _ _ dw) in H33; auto.
        elim (Q'_Ord_irReflex dw dw); auto.
      * pose proof H33. apply mt_Q'0_Q'Abs in H33; auto.
        apply φz_is_Function_Lemma1 in H34; auto.
        assert (x - Q'0 = x).
        { apply Q'_Minus_Plus; auto.
          rewrite Q'_Plus_Commutation,Q'_Plus_Property; auto. }
        rewrite H35,H33,H28 in H34. destruct H34. rewrite H34 in H32.
        elim (Q'_Ord_irReflex dw dw); auto. apply (Q'_Ord_Trans dw) in H34; auto.
        elim (Q'_Ord_irReflex dw dw); auto.
        apply Q'_N_propersubset_Q'_Z,Q'0_in_Q'_N; auto.
      * elim H10. rewrite <-H28; auto.
  Close Scope q'_scope.
Qed.

(* 实数的阿基米德性. *)
Property R_Archimedes : ∀ r, r ∈ Ｒ -> ∃ n, n ∈ Ｎ /\ (|r| = n \/ |r| < n).
Proof.
  assert (∀ r, r ∈ Ｒ -> R0 < r -> ∃ n, n ∈ Ｎ /\ (|r| = n \/ |r| < n)).
  { intros. pose proof H. inR H1 q'. pose proof H0.
    rewrite H3 in H4. apply R_Ord_Instantiate in H4 as []; auto with Q'.
    pose proof H1. apply AxiomII in H6 as [_[H6[n[]]]].
    apply mt_R0_RAbs in H0; apply mt_Q'0_Q'Abs in H4; auto.
    rewrite H0,H4 in *. set (m := \[n\]).
    assert (m ∈ Ｒ).
    { apply R_Instantiate2; auto.  apply Q'_N_propersubset_Q'_Arch; auto. }
    exists m. split. apply AxiomII; split; eauto. destruct H8.
    - left. unfold m. rewrite H3,H8; auto.
    - apply Q'_Ord_to_R_Ord in H8; auto. rewrite H3; auto.
      apply Q'_N_propersubset_Q'_Arch; auto. }
  intros. pose proof R0_in_R. assert (r ∈ Ｒ /\ R0 ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri r R0) in H2 as [H2|[]]; auto; clear H3.
  - apply R_Plus_PrOrder_Corollary in H2 as [r0[[H2[]]_]]; auto.
    assert (|r| = |r0|). { apply Neg_RAbs_Equ; auto. }
    rewrite H5. apply H; auto.
  - exists R0. split. apply R0_in_N; auto. left. apply eq_R0_RAbs; auto.
Qed.

(* Q在R中稠密的引理：对一切正数r都存在有大于该数的最小自然数n满足 r < n <= r+1. *)
Lemma Q_Density_Lemma : ∀ r, r ∈ Ｒ -> R0 < r
  -> ∃ n, n ∈ Ｎ /\ r < n /\ (n = r + R1 \/ n < r + R1).
Proof.
  intros. set (A := \{ λ u, u ∈ Ｎ /\ r < u \}).
  assert (A <> 0).
  { apply NEexE. apply mt_R0_RAbs in H0; auto.
    pose proof H. apply R_Archimedes in H1 as [n[H1[]]]; auto.
    - pose proof R1_in_N . exists (n + R1).
      pose proof H1. apply (N_Plus_in_N n R1) in H4; auto.
      apply AxiomII; repeat split; eauto. pose proof R0_lt_R1.
      apply (R_Plus_PrOrder _ _ r) in H5; try apply R0_in_R; try apply R1_in_R;
      auto. rewrite R_Plus_Property in H5; auto. rewrite <-H2,H0; auto.
    - exists n. apply AxiomII; repeat split; eauto. rewrite <-H0; auto. }
  destruct R_Ord_WellOrder_N as [_ H2].
  assert (A ⊂ Ｎ /\ A <> 0) as [].
  { split; auto. unfold Included; intros. apply AxiomII in H3; tauto. }
  apply H2 in H3; auto; clear H4. destruct H3 as [n[]]. exists n.
  apply AxiomII in H3 as [H3[]]. repeat split; auto. pose proof H5.
  apply N_propersubset_R in H7; auto. pose proof R1_in_R. pose proof H.
  apply (R_Plus_in_R r R1) in H9; auto.
  assert (n ∈ Ｒ /\ (r + R1) ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri n (r + R1)) in H10 as [H10|[]]; auto; clear H11.
  set (n1 := n - R1). assert (n1 ∈ Ｎ).
  { assert (n1 ∈ Ｒ). { apply R_Minus_in_R; auto. }
    assert (R1 + n1 = n). { apply R_Minus_Plus; auto. }
    assert (R0 ∈ Ｒ). { apply R0_in_R; auto. }
    assert (R0 < n1).
    { apply (R_Ord_Trans _ r); auto. apply (R_Plus_PrOrder _ _ R1); auto;
      rewrite H12,R_Plus_Commutation; auto. }
    rewrite N_equ_Z_me_R0; auto. apply AxiomII; repeat split; eauto.
    apply Z_Minus_in_Z; auto. apply N_propersubset_Z; auto. apply R1_in_Z; auto. }
  pose proof H11. apply N_propersubset_R in H12; auto.
  assert (n1 ∈ A).
  { apply AxiomII; repeat split; eauto. apply (R_Plus_PrOrder _ _ R1); auto.
    rewrite R_Plus_Commutation; auto. unfold n1.
    rewrite <-R_Mix_Association1,(R_Plus_Commutation _ n),
    R_Mix_Association1,R_Minus_Property1,R_Plus_Property; auto. }
  apply H4 in H13. elim H13. unfold n1. apply (R_Plus_PrOrder _ _ R1); auto.
  rewrite <-R_Mix_Association1,(R_Plus_Commutation _ n),
  R_Mix_Association1,R_Minus_Property1; auto.
  apply R_Plus_PrOrder; auto. apply R0_in_R; auto. apply R0_lt_R1; auto.
Qed.

(* 引理: Q在R中稠密的弱表达. 任意正实数 0 < u < v, 存在有理数w, u < w < v  *)
Lemma Q_Density_Weak : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> R0 < u -> u < v
  -> ∃ w, w ∈ Ｑ /\ u < w /\ w < v.
Proof.
  intros. set (vju := v - u). assert (vju ∈ Ｒ). { apply R_Minus_in_R; auto. }
  pose proof H2. apply R_Plus_PrOrder_Corollary in H4 as [a[[H4[]]_]]; auto.
  assert (vju = a). { apply R_Minus_Plus; auto. }
  assert (a <> R0).
  { intro. rewrite <-H8 in H5. elim (R_Ord_irReflex a a); auto. }
  pose proof H4. apply R_Inv in H9 as [a1[[H9[]]_]]; auto.
  assert (R0 < a1).
  { apply (R_Mult_PrOrder _ _ a); auto. apply R0_in_R; auto.
    rewrite R_Mult_Property1,H11; auto. apply R0_lt_R1; auto. }
  pose proof H9. apply R_Archimedes in H13 as [n[]]; auto. set (n1 := n + R1).
  assert (n1 ∈ Ｎ). { apply N_Plus_in_N; try apply R1_in_N; auto. }
  assert (a1 < n1).
  { pose proof H12. apply mt_R0_RAbs in H16; auto. rewrite H16 in H14.
    assert (n < n1).
    { pose proof R0_lt_R1. apply (R_Plus_PrOrder _ _ n) in H17;
      try apply R0_in_R; try apply R1_in_R; auto.
      rewrite R_Plus_Property in H17; auto. apply N_propersubset_R; auto.
      apply N_propersubset_R; auto. }
    destruct H14. rewrite H14; auto. apply (R_Ord_Trans _ n); auto;
    try apply N_propersubset_R; auto. } clear H13 H14.
  set (n1v := n1 · v). set (n1u := (n1 · u) + R1).
  assert (n1u ∈ Ｒ /\ n1v ∈ Ｒ) as [].
  { split; try apply R_Plus_in_R; try apply R_Mult_in_R; auto;
    try apply R1_in_R; try apply N_propersubset_R; auto. }
  pose proof H15. apply N_propersubset_R in H17; auto.
  assert (n1u < n1v).
  { apply (R_Mult_PrOrder _ _ a) in H16; auto.
    rewrite H11,R_Mult_Commutation,<-H7 in H16; auto.
    unfold vju in H16. rewrite R_Mult_Distribution_Minus in H16; auto.
    apply (R_Plus_PrOrder _ _ (n1 · u)) in H16; auto;
    try apply R_Minus_in_R; try apply R_Mult_in_R; try apply R1_in_R; auto.
    rewrite <-R_Mix_Association1,(R_Plus_Commutation _ (n1 · v)),
    R_Mix_Association1,R_Minus_Property1,R_Plus_Property in H16;
    try apply R_Mult_in_R; auto. }
  assert ((n1 · u) ∈ Ｒ). { apply R_Mult_in_R; auto. }
  assert (R0 < (n1 · u)).
  { apply (R_Mult_PrOrder _ _ n1) in H1; auto with R.
    rewrite R_Mult_Property1 in H1; auto.
    apply (R_Ord_Trans _ a1); auto. apply R0_in_R; auto. }
  pose proof H19. apply Q_Density_Lemma in H21 as [m[H21[]]]; auto.
  assert (m < (n1 · v)).
  { destruct H23. rewrite H23; auto. apply (R_Ord_Trans _ n1u); auto.
    apply N_propersubset_R; auto. } clear H23.
  assert (R0 < n1). { apply (R_Ord_Trans _ a1); auto. apply R0_in_R; auto. }
  assert (n1 <> R0).
  { intro. rewrite <-H25 in H23. elim (R_Ord_irReflex n1 n1); auto. }
  pose proof H17. apply R_Inv in H26 as [n1'[[H26[]]_]]; auto.
  pose proof H21. apply N_propersubset_R in H29; auto. set (q := m · n1').
  assert (q ∈ Ｒ). { apply R_Mult_in_R; auto. }
  assert (q ∈ Ｑ).
  { rewrite Q_equ_Z_Div; auto. apply AxiomII; repeat split; eauto.
    exists m,n1. repeat split. apply N_propersubset_Z; auto.
    apply MKT4'; split. apply N_propersubset_Z; auto.
    apply AxiomII; split; eauto. intro. pose proof R0_in_Q.
    apply MKT41 in H31; eauto. unfold q. symmetry. apply R_Divide_Mult; auto.
    rewrite R_Mult_Commutation,R_Mult_Association,
    (R_Mult_Commutation n1'),H28,R_Mult_Property2; auto. }
  assert ((n1 · q) = m).
  { unfold q. rewrite (R_Mult_Commutation m),<-R_Mult_Association,H28,
   (R_Mult_Commutation _ m),R_Mult_Property2; auto. apply R1_in_R; auto. }
  exists q. repeat split; auto; apply (R_Mult_PrOrder _ _ n1); auto;
  rewrite H32; auto.
Qed.

(* Q在R中稠密. 任意实数 u < v, 存在有理数q, u < q < v  *)
Property Q_Density : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> u < v
  -> ∃ q, q ∈ Ｑ /\ u < q /\ q < v.
Proof.
  intros. pose proof R0_in_R. assert (R0 ∈ Ｒ /\ u ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri _ u) in H3 as []; auto; clear H4.
  - apply Q_Density_Weak; auto.
  - assert (∃ n, n ∈ Ｎ /\ R0 < (u + n)) as [n[]].
    { destruct H3.
      - pose proof H3. apply R_Plus_PrOrder_Corollary in H4 as [u0[[H4[]]_]]; auto.
        pose proof H5. apply mt_R0_RAbs in H7; auto.
        pose proof H4. apply Q_Density_Lemma in H8 as [m[H8[H9 _]]]; auto.
        exists m. split; auto. pose proof H8. apply N_propersubset_R in H10; auto.
        apply (R_Plus_PrOrder _ _ u0); auto. apply R_Plus_in_R; auto.
        rewrite R_Plus_Property,<-R_Plus_Association,
        (R_Plus_Commutation u0),H6,R_Plus_Commutation,R_Plus_Property; auto.
      - pose proof R1_in_N. exists R1. split; auto. pose proof R1_in_R.
        rewrite R_Plus_Commutation,<-H3,R_Plus_Property; auto.
        apply R0_lt_R1; auto. }
    pose proof H4. apply N_propersubset_R in H6; auto.
    pose proof H1. apply (R_Plus_PrOrder _ _ n) in H7; auto.
    pose proof H7. apply Q_Density_Weak in H8 as [q[H8[]]];
    try apply R_Plus_in_R; try rewrite R_Plus_Commutation; auto.
    set (q1 := q - n). assert (q1 ∈ Ｑ).
    { apply Q_Minus_in_Q; auto. apply Z_propersubset_Q,N_propersubset_Z; auto. }
    assert (n + q1 = q). { apply R_Minus_Plus; auto; apply Q_subset_R; auto. }
    exists q1. pose proof H11. apply Q_subset_R in H13; auto.
    repeat split; auto; apply (R_Plus_PrOrder _ _ n); try rewrite H12; auto.
Qed.

