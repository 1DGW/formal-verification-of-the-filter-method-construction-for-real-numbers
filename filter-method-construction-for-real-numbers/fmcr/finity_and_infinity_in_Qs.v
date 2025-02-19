(*  This file presents the formalization of non-standard numbers in *Q.  *)
(*   It is developmented in the CoqIDE (version 8.13.2) for windows.     *)

(** finity_and_infinity_in_Qs *)

Require Export fmcr.N_Z_Q_in_Qs.

(* *Q 中的阿基米德(Archimedes)序域 *Q_Arch *)
Definition Q'_Arch := \{ λ u, u ∈ Q' /\ ∃ k, k ∈ Q'_N /\ (|u| = k \/ |u| < k) \}.

Property Q'_Arch_subset_Q' : Q'_Arch ⊂ Q'.
Proof. unfold Included; intros. apply AxiomII in H; tauto. Qed.

Property Q'_Arch_is_Set : Ensemble Q'_Arch.
Proof.
  intros. apply (MKT33 Q'). apply Q'_is_Set; auto. apply Q'_Arch_subset_Q'.
Qed.

Property Q'0_in_Q'_Arch : Q'0 ∈ Q'_Arch.
Proof.
  pose proof Q'0_in_Q'. apply AxiomII; repeat split; eauto. exists Q'0. split.
  - destruct φ4_is_Function as [[][]]. replace Q'_N with (ran(φ4)); auto.
    rewrite <-φ4_0; auto. apply (@ Property_ran 0),Property_Value; auto.
    rewrite H2. apply in_ω_0.
  - left. apply eq_Q'0_Q'Abs; auto.
Qed.

Global Hint Resolve Q'0_in_Q'_Arch : Q'.

Property Q'1_in_Q'_Arch : Q'1 ∈ Q'_Arch.
Proof.
  pose proof Q'1_in_Q'. apply AxiomII; repeat split; eauto. exists Q'1. split.
  - destruct φ4_is_Function as [[][]]. replace Q'_N with (ran(φ4)); auto.
    rewrite <-φ4_1; auto. apply (@ Property_ran 1),Property_Value; auto.
    rewrite H2. apply in_ω_1.
  - left. apply mt_Q'0_Q'Abs; auto. apply Q'0_lt_Q'1.
Qed.

Global Hint Resolve Q'1_in_Q'_Arch : Q'.

(* *Q_Arch对加法封闭 *)
Property Q'_Arch_Plus_in_Q'_Arch : ∀ u v, u ∈ Q'_Arch -> v ∈ Q'_Arch
  -> (u + v) ∈ Q'_Arch.
Proof.
  intros. apply AxiomII in H as [H[H1[m[]]]].
  apply AxiomII in H0 as [H0[H4[n[]]]]. pose proof H1.
  apply (Q'_Plus_in_Q' u v) in H7; auto. apply AxiomII; repeat split; eauto.
  pose proof H1. apply (Q'Abs_inEqu u v) in H8; auto.
  assert ((m + n) ∈ Q'_N).
  { destruct φ4_is_Function as [[][]].
    assert (m ∈ ran(φ4) /\ n ∈ ran(φ4)) as []; auto.
    rewrite reqdi in H13,H14. apply Property_Value,Property_ran in H13;
    apply Property_Value,Property_ran in H14; auto.
    rewrite <-deqri,H11 in H13,H14. pose proof H13.
    apply (φ4_PrPlus _ ((φ4⁻¹)[n])) in H15; auto.
    rewrite f11vi,f11vi in H15; auto. pose proof H13.
    apply (ω_Plus_in_ω _ ((φ4⁻¹)[n])) in H16; auto. rewrite <-H11 in H16.
    apply Property_Value,Property_ran in H16; auto. rewrite H15 in H16; auto. }
  exists (m + n). split; auto. pose proof H2; pose proof H5.
  apply Q'_N_subset_Q' in H10; apply Q'_N_subset_Q' in H11; auto.
  assert (|u| + |v| = m + n \/ |u| + |v| < m + n).
  { destruct H3,H6.
    - rewrite H3,H6; auto.
    - rewrite H3. right. apply Q'_Plus_PrOrder; auto. apply Q'Abs_in_Q'; auto.
    - rewrite H6. right. rewrite Q'_Plus_Commutation,(Q'_Plus_Commutation _ n);
      auto. apply Q'_Plus_PrOrder; auto. apply Q'Abs_in_Q'; auto.
      apply Q'Abs_in_Q'; auto.
    - apply (Q'_Plus_PrOrder _ _ m) in H6; try apply Q'Abs_in_Q'; auto.
      apply (Q'_Plus_PrOrder _ _ |v|) in H3; try apply Q'Abs_in_Q'; auto.
      rewrite Q'_Plus_Commutation in H6; try apply Q'Abs_in_Q'; auto.
      right. apply (Q'_Ord_Trans _ (|v| + m)); try apply Q'_Plus_in_Q';
      try apply Q'Abs_in_Q'; auto.
      rewrite Q'_Plus_Commutation; try apply Q'Abs_in_Q'; auto. }
  destruct H8,H12.
  - rewrite H8,H12; auto.
  - rewrite H8; auto.
  - rewrite <-H12; auto.
  - right. apply (Q'_Ord_Trans _ (|u| + |v|)); try apply Q'_Plus_in_Q';
    try apply Q'Abs_in_Q'; try apply Q'Abs_in_Q'; auto.
Qed.

Global Hint Resolve Q'_Arch_Plus_in_Q'_Arch : Q'.

(* *Q_Arch对乘法封闭 *)
Property Q'_Arch_Mult_in_Q'_Arch : ∀ u v, u ∈ Q'_Arch -> v ∈ Q'_Arch
  -> (u · v) ∈ Q'_Arch.
Proof.
  intros. apply AxiomII in H as [H[H1[m[]]]].
  apply AxiomII in H0 as [H0[H4[n[]]]]. pose proof H1.
  apply (Q'_Mult_in_Q' u v) in H7; auto. apply AxiomII; repeat split; eauto.
  pose proof H1. apply (Q'Abs_PrMult u v) in H8; auto.
  assert ((m · n) ∈ Q'_N).
  { destruct φ4_is_Function as [[][]].
    assert (m ∈ ran(φ4) /\ n ∈ ran(φ4)) as []; auto. rewrite reqdi in H13,H14.
    apply Property_Value,Property_ran in H13;
    apply Property_Value,Property_ran in H14; auto.
    rewrite <-deqri,H11 in H13,H14. pose proof H13.
    apply (φ4_PrMult _ ((φ4⁻¹)[n])) in H15; auto.
    rewrite f11vi,f11vi in H15; auto. pose proof H13.
    apply (ω_Mult_in_ω _ ((φ4⁻¹)[n])) in H16; auto.
    rewrite <-H11 in H16. apply Property_Value,Property_ran in H16; auto.
    rewrite H15 in H16; auto. }
  exists (m · n). split; auto. pose proof H2; pose proof H5.
  apply Q'_N_subset_Q' in H10; apply Q'_N_subset_Q' in H11; auto.
  assert (∀ w, w ∈ Q'_N -> w <> Q'0 -> Q'0 < w).
  { intros. pose proof Q'0_in_Q'. pose proof H12. apply Q'_N_subset_Q' in H12.
    assert (Q'0 ∈ Q' /\ w ∈ Q') as []; auto.
    apply (Q'_Ord_Tri _ w) in H16 as [H16|[]]; auto; clear H17; elim H13; auto.
    destruct φ4_is_Function as [[][]]. assert (w ∈ ran(φ4)); auto.
    rewrite reqdi in H21. apply Property_Value,Property_ran in H21; auto.
    rewrite <-deqri,H19 in H21.
    assert (w = φ4[(φ4⁻¹)[w]]). { rewrite f11vi; auto. }
    rewrite H22,<-φ4_0 in H16; auto. apply φ4_PrOrder in H16; auto.
    elim (@ MKT16 ((φ4⁻¹)[w])); auto. }
  destruct H3,H6.
  - left. rewrite H8,H3,H6; auto.
  - destruct (classic (m = Q'0)). left. rewrite H8,H3,H13,
    Q'_Mult_Commutation,Q'_Mult_Property1,Q'_Mult_Commutation,
    Q'_Mult_Property1; try apply Q'Abs_in_Q'; try apply Q'0_in_Q'; auto.
    right. apply (Q'_Mult_PrOrder _ _ m) in H6; auto.
    rewrite H8,H3; auto. apply Q'Abs_in_Q'; auto.
  - destruct (classic (n = Q'0)). left. rewrite H8,H6,H13,
    Q'_Mult_Property1,Q'_Mult_Property1; try apply Q'Abs_in_Q'; auto.
    right. apply (Q'_Mult_PrOrder _ _ n) in H3; try apply Q'Abs_in_Q'; auto.
    rewrite Q'_Mult_Commutation,(Q'_Mult_Commutation n) in H3;
    try apply Q'Abs_in_Q'; auto. rewrite H8,H6; auto.
  - pose proof H1; pose proof H4.
    apply (Q'0_le_Q'Abs u) in H13 as [];
    apply (Q'0_le_Q'Abs v) in H14 as []; auto.
    assert (Q'0 < m /\ Q'0 < n) as [].
    { split.
      - destruct H15. rewrite <-H15; auto. apply (Q'_Ord_Trans _ |u|); auto.
        apply Q'0_in_Q'; auto.
      - destruct H16. rewrite <-H16; auto. apply (Q'_Ord_Trans _ |v|); auto.
        apply Q'0_in_Q'; auto. }
    apply (Q'_Mult_PrOrder _ _ m) in H6; auto. destruct H16.
    + rewrite H16,Q'_Mult_Property1 in H6; auto. right.
      rewrite H8,H16,Q'_Mult_Property1; auto.
    + apply (Q'_Mult_PrOrder _ _ |v|) in H3; auto.
      rewrite Q'_Mult_Commutation,(Q'_Mult_Commutation _ m) in H3; auto.
      right. rewrite H8. apply (Q'_Ord_Trans _ (m · |v|));
      try apply Q'_Mult_in_Q'; auto.
Qed.

Global Hint Resolve Q'_Arch_Mult_in_Q'_Arch : Q'.

(* *Q_Arch对减法封闭 *)
Property Q'_Arch_Minus_in_Q'_Arch : ∀ u v, u ∈ Q'_Arch -> v ∈ Q'_Arch
  -> (u - v) ∈ Q'_Arch.
Proof.
  intros. assert (u ∈ Q' /\ v ∈ Q') as [].
  { apply Q'_Arch_subset_Q' in H; apply Q'_Arch_subset_Q' in H0; auto. }
  pose proof H1. apply (Q'_Minus_in_Q' u v) in H3; auto.
  assert (|(u - v)| = |u| + |v| \/ |(u - v)| < |u| + |v|).
  { pose proof H2. apply Q'_Neg in H4 as [v0[[]]]; auto. clear H6.
    assert (u - v = u + v0).
    { apply Q'_Minus_Plus; try apply Q'_Plus_in_Q'; auto.
      rewrite <-Q'_Plus_Association,(Q'_Plus_Commutation v),
      Q'_Plus_Association,H5,Q'_Plus_Property; auto. }
    assert (|v| = |v0|). { apply Neg_Q'Abs_Equ; auto. }
    rewrite H6,H7. apply Q'Abs_inEqu; auto. }
  apply AxiomII in H as [H[H5[k1[]]]]. apply AxiomII in H0 as [H0[H8[k2[]]]].
  apply AxiomII; repeat split; eauto. exists (k1 + k2).
  assert (k1 ∈ Q' /\ k2 ∈ Q') as []. { split; try apply Q'_N_subset_Q'; auto. }
  assert ((k1 + k2) ∈ Q'_N). { apply Q'_N_Plus_in_Q'_N; auto. }
  assert (|u| + |v| = k1 + k2 \/ (|u| + |v|) < k1 + k2).
  { destruct H7,H10.
    - rewrite H7,H10; auto.
    - right. rewrite H7. apply Q'_Plus_PrOrder; auto. apply Q'Abs_in_Q'; auto.
    - right. rewrite H10,Q'_Plus_Commutation,
      (Q'_Plus_Commutation k1); try apply Q'Abs_in_Q'; auto.
      apply Q'_Plus_PrOrder; try apply Q'Abs_in_Q'; auto.
    - right. apply (Q'_Plus_PrOrder _ _ k1) in H10; try apply Q'Abs_in_Q'; auto.
      apply (Q'_Ord_Trans _ (k1 + |v|)); try apply Q'_Plus_in_Q';
      try apply Q'Abs_in_Q'; auto.
      rewrite Q'_Plus_Commutation,(Q'_Plus_Commutation k1);
      try apply Q'Abs_in_Q'; auto.
      apply Q'_Plus_PrOrder; try apply Q'Abs_in_Q'; auto. }
  split; auto. destruct H4,H14.
  - rewrite H4,H14; auto.
  - right. rewrite H4; auto.
  - right. rewrite <-H14; auto.
  - right. apply (Q'_Ord_Trans _ (|u| + |v|));
    try apply Q'_Plus_in_Q'; try apply Q'Abs_in_Q'; auto.
Qed.

Global Hint Resolve Q'_Arch_Minus_in_Q'_Arch : Q'.

Property Q'_N_propersubset_Q'_Arch : Q'_N ⊂ Q'_Arch /\ Q'_N <> Q'_Arch.
Proof.
  split.
  - unfold Included; intros. pose proof H. apply Q'_N_subset_Q' in H0; auto.
    apply AxiomII; repeat split; eauto. exists z. split; auto.
    destruct (classic (z = Q'0)).
    + pose proof H1. apply eq_Q'0_Q'Abs in H1; auto. rewrite H1; auto.
    + assert (z ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. pose proof Q'0_in_Q'. apply MKT41 in H2; eauto. }
      apply Q'_N_Q'0_is_FirstMember,mt_Q'0_Q'Abs in H2; auto.
  - intro. pose proof Q'0_in_Q'. pose proof Q'1_in_Q'. set (A := (Z'1 + Z'1)%z').
    assert (Z'0 < A)%z'.
    { pose proof Z'0_lt_Z'1. pose proof H2.
      apply (Z'_Plus_PrOrder _ _ Z'1) in H3; auto with Z'.
      rewrite Z'_Plus_Property in H3; auto with Z'.
      apply (Z'_Ord_Trans Z'0) in H3; auto with Z'. }
    assert (A ∈ (Z' ~ [Z'0])).
    { apply MKT4'; split; [unfold A| ]; auto with Z'.
      apply AxiomII; split. assert (A ∈ Z').
      { apply Z'_Plus_in_Z'; auto with Z'. }
      eauto. intro. apply MKT41 in H3. rewrite H3 in H2.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'. pose proof Z'0_in_Z'. eauto. }
    set (a := \[[Z'1,A]\]).
    assert (a ∈ Q'). { apply Q'_Instantiate2; auto with Z'. }
    assert (Q'0 < a).
    { rewrite Q'0_Property; auto. apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Commutation,Z'_Mult_Property1,Z'_Mult_Property2;
      unfold A; auto with Z'. }
    assert (a < Q'1).
    { rewrite Q'1_Property; auto. apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Property2; unfold A; auto with Z'.
      pose proof Z'0_lt_Z'1. apply (Z'_Plus_PrOrder _ _ Z'1) in H6; auto with Z'.
      rewrite Z'_Plus_Property in H6; auto with Z'. }
    assert (Q'0 ∈ Q'_N).
    { pose proof in_ω_0. destruct φ4_is_Function as [[][]]. rewrite <-H10 in H7.
      apply Property_Value,Property_ran in H7; auto. rewrite φ4_0 in H7; auto. }
    assert (Q'1 ∈ Q'_N).
    { pose proof in_ω_1. destruct φ4_is_Function as [[][]]. rewrite <-H11 in H8.
      apply Property_Value,Property_ran in H8; auto. rewrite φ4_1 in H8; auto. }
    assert (a ∈ Q'_Arch).
    { apply AxiomII; repeat split; eauto. exists Q'1. split; auto. right.
      rewrite mt_Q'0_Q'Abs; auto. }
    rewrite <-H in H9. destruct φ4_is_Function as [[][]].
    pose proof φ4_0. pose proof φ4_1. assert (a ∈ ran(φ4)); auto.
    rewrite reqdi in H16. apply Property_Value,Property_ran in H16; auto.
    rewrite <-deqri,H12 in H16. assert (φ4[(φ4⁻¹)[a]] = a). { rewrite f11vi; auto. }
    rewrite <-H14,<-H17 in H5. rewrite <-H15,<-H17 in H6.
    pose proof in_ω_0; pose proof in_ω_1.
    apply φ4_PrOrder in H5; apply φ4_PrOrder in H6; auto.
    apply MKT41 in H6; eauto. rewrite H6 in H5. elim (@ MKT16 0); auto.
Qed.

(* *Q_Z是*Q_Arch的真子集. 也就是说, *Q_Z中的元素都是有限可测的. *)
Property Q'_Z_propersubset_Q'_Arch : Q'_Z ⊂ Q'_Arch /\ Q'_Z <> Q'_Arch.
Proof.
  split.
  - unfold Included; intros. pose proof H. apply AxiomII in H as [H[x[]]].
    pose proof H1. apply Z'_Z_subset_Z' in H3.
    assert (z ∈ Q').
    { rewrite H2. apply Q'_Instantiate2; auto with Z'. }
    apply AxiomII; repeat split; auto. assert (Q'0 ∈ Q' /\ z ∈ Q') as [].
    { split; try apply Q'0_in_Q'; auto. }
    apply (Q'_Ord_Tri _ z) in H5 as [H5|[]]; auto; clear H6.
    + pose proof H5. apply mt_Q'0_Q'Abs in H6; auto. rewrite H6. exists z.
      split; auto. rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; auto.
    + assert (z ∈ \{ λ u, u ∈ Q'_Z /\ u < Q'0 \}). { apply AxiomII; auto. }
      rewrite Q'_N_Neg_equ_Q'_Z_lt_Q'0 in H6; auto.
      apply AxiomII in H6 as [H6[H7[z0[]]]]. pose proof H8.
      apply Q'_N_Q'0_is_FirstMember in H8; auto. apply lt_Q'0_Q'Abs in H5; auto.
      apply MKT4' in H10 as [H10 _]. apply Q'_Minus_Plus in H9;
      try apply Q'0_in_Q'; auto. rewrite H9 in H5. exists z0. split; auto.
      apply Q'_N_subset_Q'; auto.
    + exists z. symmetry in H5. pose proof H5. apply eq_Q'0_Q'Abs in H5; auto.
      rewrite H5,H6. split; auto. apply Q'0_in_Q'_N; auto.
  - intro. set (two := (Z'1 + Z'1)%z').
    assert (two ∈ (Z' ~ [Z'0])).
    { assert (two ∈ Z'). { unfold two; auto with Z'. }
      apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. pose proof Z'0_in_Z'. apply MKT41 in H1; eauto.
      pose proof Z'0_lt_Z'1. pose proof H3.
      apply (Z'_Plus_PrOrder _ _ Z'1) in H4; auto with Z'. unfold two in H1.
      rewrite Z'_Plus_Property,H1 in H4; auto with Z'.
      apply (Z'_Ord_Trans Z'0) in H4; auto with Z'.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'. }
    set (dw := \[[Z'1,two]\]). Z'split H0. assert (Z'0 < two)%z'.
    { unfold two. apply (Z'_Ord_Trans _ Z'1); auto with Z'.
      pose proof Z'0_lt_Z'1. apply (Z'_Plus_PrOrder _ _ Z'1) in H3; auto with Z'.
      rewrite Z'_Plus_Property in H3; auto with Z'. }
    assert (dw ∈ Q'). { apply Q'_Instantiate2; auto with Z'. }
    assert (Q'0 < dw).
    { rewrite Q'0_Property; auto. unfold dw.
      apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Commutation,Z'_Mult_Property1,Z'_Mult_Property2;
      auto with Z'. }
    assert (dw < Q'1).
    { unfold dw. rewrite Q'1_Property; auto. apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Property2; auto with Z'.
      replace Z'1 with (Z'1 + Z'0)%z'. unfold two.
      apply Z'_Plus_PrOrder; auto with Z'. apply Z'_Plus_Property; auto with Z'. }
    assert (dw ∈ Q'_Arch).
    { apply AxiomII; repeat split; eauto. exists Q'1. apply mt_Q'0_Q'Abs in H5;
      auto. rewrite H5. split; auto. apply Q'1_in_Q'_N; auto. }
    rewrite <-H in H7. assert (dw ∈ Q'_N).
    { rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; repeat split; eauto. }
    destruct φ4_is_Function as [[][]]. assert (dw ∈ ran(φ4)); auto.
    rewrite reqdi in H13. apply Property_Value,Property_ran in H13; auto.
    rewrite <-deqri,H11 in H13.
    assert (dw = φ4[(φ4⁻¹)[dw]]). { rewrite f11vi; auto. }
    rewrite H14,<-φ4_0 in H5; auto. rewrite H14,<-φ4_1 in H6; auto.
    pose proof in_ω_0; pose proof in_ω_1.
    apply φ4_PrOrder in H5; apply φ4_PrOrder in H6; auto.
    apply MKT41 in H6; eauto. rewrite H6 in H5. elim (@ MKT16 0); auto.
Qed.

(* *Q_Q是*Q_Arch的子集. 也就是说, *Q_Q中的元素都是有限可测的. *)
Property Q'_Q_subset_Q'_Arch : Q'_Q ⊂ Q'_Arch.
Proof.
  Open Scope z'_scope.
  unfold Included. intros q H. pose proof H. apply Q'_Q_subset_Q' in H0; auto.
  apply AxiomII in H as [H[u[v[H1[]]]]]. apply AxiomII; repeat split; auto.
  pose proof H1. apply Z'_Z_subset_Z' in H4; auto. Z'split1 H2 H5.
  Q'altH H3 u v v. set (V2 := v · v). set (U := v · u).
  assert (Z'0 < V2). unfold V2. auto with Z'.
  assert (V2 ∈ (Z'_Z ~ [Z'0])).
  { assert (V2 ∈ Z'_Z).
    { apply MKT4' in H2 as []. apply Z'_Z_Mult_in_Z'_Z; auto. }
    apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
    pose proof Z'0_in_Z'. apply MKT41 in H10; eauto. rewrite H10 in H8.
    elim (Z'_Ord_irReflex Z'0 Z'0); auto. }
  Z'split1 H9 H10. apply MKT4' in H2 as [H2 _].
  assert (U ∈ Z'_Z). { apply Z'_Z_Mult_in_Z'_Z; auto. }
  pose proof H13. apply Z'_Z_subset_Z' in H14; auto.
  assert (U ∈ Z' /\ Z'0 ∈ Z') as []. { split; auto with Z'. }
  apply (Z'_Ord_Tri _ Z'0) in H15 as []; auto; clear H16.
  - pose proof H15. apply Z'_Plus_PrOrder_Corollary in H16
    as [U0[[H16[]]]]; auto with Z'.
    assert (U0 ∈ Z'_Z).
    { apply AxiomII in H13 as [_[M[N[H13[]]]]].
      set (U1 := (\[[N,M]\])%n'). assert (Ensemble U1).
      { apply (MKT33 (N' × N')). apply MKT74; apply N'_is_Set.
        unfold Included; intros. apply AxiomII in H22; tauto. }
      assert (U + U1 = Z'0).
      { unfold U1. rewrite H21,Z'_Plus_Instantiate,
        N'_Plus_Commutation,Z'0_Property; try apply N'_N_subset_N'; auto.
        apply R_N'_Property; try apply N'_Plus_in_N'; try apply Fn_in_N';
        try apply in_ω_0; auto; apply N'_N_subset_N'; auto. }
      assert (U1 ∈ Z'_Z). { apply AxiomII; split; eauto. }
      assert (U0 = U1).
      { apply H19. repeat split; auto. apply Z'_Z_subset_Z'; auto.
        apply (Z'_Plus_PrOrder _ _ U); auto. apply Z'0_in_Z'; auto.
        apply Z'_Z_subset_Z'; auto. rewrite Z'_Plus_Property,H23; auto. }
      rewrite H25; auto. }
    set (qa := (\[[U0,Z'1]\])%q').
    assert (qa ∈ Q'). { apply Q'_Instantiate2; auto with Z'. }
    assert (qa ∈ Q'_Z). {  apply AxiomII; split; eauto. }
    assert (Q'0 < qa)%q'.
    { rewrite Q'0_Property; auto. apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Commutation,Z'_Mult_Property1,
      Z'_Mult_Commutation,Z'_Mult_Property2; auto with Z'. }
    exists qa. split.
    + rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; split; eauto.
    + assert (|q| = \[[U0,V2]\])%q'.
      { assert (\[[U0,V2]\] = Q'0 - q)%q'.
        { symmetry. apply Q'_Minus_Plus;
          try apply Q'0_in_Q'; auto. apply Q'_Instantiate2; auto.
          rewrite H3,Q'_Plus_Instantiate,Q'0_Property; auto with Z'.
          apply R_Z'_Property; auto with Z'.
          rewrite Z'_Mult_Property1,Z'_Mult_Property2; auto with Z'.
          replace (v · u) with U; auto.
          replace (v · v) with V2; auto.
          rewrite Z'_Mult_Commutation,<-Z'_Mult_Distribution,
          H18,Z'_Mult_Property1; auto. }
        rewrite H24. apply lt_Q'0_Q'Abs; auto. rewrite H3,Q'0_Property; auto.
        replace (v · u) with U; auto. replace (v · v) with V2; auto.
        apply Q'_Ord_Instantiate; auto with Z'.
        rewrite Z'_Mult_Property2,Z'_Mult_Property1; auto. }
      rewrite H24. pose proof H8. apply Z'_otherPropertys7 in H25 as []; auto.
      * right. apply Q'_Ord_Instantiate; auto with Z'.
        rewrite (Z'_Mult_Commutation V2); auto.
        apply Z'_Mult_PrOrder; auto. apply Z'1_in_Z'; auto.
      * left. apply R_Z'_Property; auto with Z'.
        rewrite Z'_Mult_Property2,<-H25,Z'_Mult_Commutation,
        Z'_Mult_Property2; auto with Z'.
  - assert (|q| = q).
    { destruct H15. apply mt_Q'0_Q'Abs; auto. rewrite H3,Q'0_Property; auto.
      apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Commutation,Z'_Mult_Property1,
      Z'_Mult_Commutation,Z'_Mult_Property2; auto with Z'.
      assert (q = Q'0).
      { rewrite H3,Q'0_Property; auto. apply R_Z'_Property; auto with Z'.
        rewrite Z'_Mult_Property2,Z'_Mult_Property1; auto. }
      pose proof H16. apply eq_Q'0_Q'Abs in H16; auto. rewrite H16; auto. }
    set (qa := (\[[U,Z'1]\])%q').
    assert (qa ∈ Q'). { apply Q'_Instantiate2; auto with Z'. }
    assert (qa ∈ Q'_Z). {  apply AxiomII; split; eauto. }
    assert ((Q'0 = qa \/ Q'0 < qa))%q'.
    { destruct H15. right. rewrite Q'0_Property; auto.
      apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Commutation,Z'_Mult_Property1,
      Z'_Mult_Commutation,Z'_Mult_Property2; auto with Z'.
      left. unfold qa. rewrite Q'0_Property,H15; auto. }
    exists qa. split.
    + rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; split; eauto.
    + rewrite H16. pose proof H8. apply Z'_otherPropertys7 in H20 as []; auto.
      * destruct H15. right. rewrite H3.
        apply Q'_Ord_Instantiate; auto with Z'.
        rewrite (Z'_Mult_Commutation _ U); auto.
        apply Z'_Mult_PrOrder; auto. apply Z'1_in_Z'; auto. left. unfold qa.
        rewrite H3,H15. replace (v · u) with U; auto. rewrite H15.
        apply R_Z'_Property; auto with Z'.
        rewrite Z'_Mult_Property2,Z'_Mult_Property1; auto with Z'.
      * left. rewrite H3. unfold qa. unfold V2 in H20. rewrite <-H20; auto.
  Close Scope z'_scope.
Qed.

Lemma Q'_Q_propersubset_Q'_Arch_Lemma : ∀ u, u ∈ (Q'_N ~ [Q'0])
  -> Q'1 = u \/ Q'1 < u.
Proof.
  intros. pose proof H. apply Q'_N_Q'0_is_FirstMember in H; auto.
  pose proof Q'0_in_Q'; pose proof Q'1_in_Q'. apply MKT4' in H0 as [H0 _].
  assert (u ∈ Q').
  { apply Q'_Arch_subset_Q',Q'_N_propersubset_Q'_Arch; auto. }
  assert (Q'1 ∈ Q' /\ u ∈ Q') as []; auto.
  apply (Q'_Ord_Tri _ u) in H4 as [H4|[]]; auto; clear H5.
  destruct φ4_is_Function as [[][]]. assert (u ∈ ran(φ4)); auto.
  rewrite reqdi in H9. apply Property_Value,Property_ran in H9; auto.
  assert (u = φ4[(φ4⁻¹)[u]]). { rewrite f11vi; auto. }
  rewrite <-φ4_0,H10 in H; rewrite <-φ4_1,H10 in H4; auto.
  rewrite <-deqri,H7 in H9. pose proof in_ω_0; pose proof in_ω_1.
  apply φ4_PrOrder in H; apply φ4_PrOrder in H4; auto.
  apply MKT41 in H4; eauto. rewrite H4 in H. elim (@ MKT16 0); auto.
Qed.

(* *Q_Q 是 *Q_Arch 的真子集. *)
Property Q'_Q_propersubset_Q'_Arch : Q'_Q ⊂ Q'_Arch /\ Q'_Q <> Q'_Arch.
Proof.
  split. apply Q'_Q_subset_Q'_Arch; auto. destruct NPAUF. intro.
  destruct φ3_is_Function as [[][]]. destruct N'_N_propersubset_N' as [].
  assert ((N' ~ N'_N) <> Φ).
  { intro. elim H7. apply AxiomI; split; intros; auto. apply NNPP; intro.
    elim (@ MKT16 z). rewrite <-H8. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. }
  apply NEexE in H8 as [t]. pose proof H8. apply MKT4' in H9
  as [H9 _]. pose proof H9. rewrite <-H4 in H10.
  apply Property_Value,Property_ran in H10; auto.
  pose proof φ3_ran. rewrite H11 in H10,H5.
  assert (t <> F 0).
  { intro. apply (N'_Infty t (F 0)) in H8; auto. rewrite <-H12 in H8.
    elim (N'_Ord_irReflex t t); auto. apply Fn_in_N'_N,in_ω_0. }
  assert (φ3[t] <> Q'0).
  { intro. rewrite <-φ3_N'0 in H13; auto. elim H12.
    apply f11inj in H13; auto; rewrite H4; auto.
    apply Fn_in_N'; destruct H; auto. }
  set (t1 := Q'1 / φ3[t]).
  assert (t1 ∈ Q'). { unfold t1. auto with Q'. }
  assert (Q'0 < φ3[t]).
  { rewrite <-φ3_N'0; auto. apply φ3_PrOrder; auto. apply Fn_in_N'; auto.
    apply N'_Infty; auto. apply Fn_in_N'_N; auto. }
  assert (Q'0 < t1).
  { apply (Q'_Mult_PrOrder _ _ φ3[t]); auto with Q'.
    unfold t1. rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto with Q'. }
  assert (t1 ∈ Q'_Arch).
  { apply AxiomII; repeat split; eauto. exists Q'1.
    split. apply Q'1_in_Q'_N; auto. apply mt_Q'0_Q'Abs in H16; auto.
    rewrite H16. right. apply (Q'_Mult_PrOrder _ _ φ3[t]); auto with Q'.
    unfold t1. rewrite Q'_Divide_Property3,Q'_Mult_Property2; auto with Q'.
    rewrite <-φ3_N'1; auto. apply φ3_PrOrder; auto. apply Fn_in_N'; auto.
    apply in_ω_1. apply N'_Infty; auto. apply Fn_in_N'_N,in_ω_1. }
  rewrite <-H1 in H17. rewrite Q'_Q_equ_Q'_Z_Div in H17; auto.
  apply AxiomII in H17 as [_[H17[a[b[H18[]]]]]]. unfold t1 in H20.
  pose proof H18. apply Q'_Z_subset_Q' in H21; auto.
  pose proof H19. apply MKT4' in H22 as [H22 _].
  apply Q'_Z_subset_Q' in H22; auto.
  assert (b <> Q'0).
  { intro. apply MKT4' in H19 as []. apply AxiomII in H24 as [_].
    elim H24. apply MKT41; eauto with Q'. }
  apply (Q'_Mult_Cancellation φ3[t]) in H20; auto with Q'.
  rewrite Q'_Divide_Property3 in H20; auto with Q'.
  apply (Q'_Mult_Cancellation b) in H20; auto with Q'.
  rewrite Q'_Mult_Property2,<-Q'_Mult_Association,
  (Q'_Mult_Commutation b),Q'_Mult_Association,
  Q'_Divide_Property3 in H20; auto with Q'.
  assert (a <> Q'0).
  { intro. rewrite H24,Q'_Mult_Property1 in H20; auto. }
  pose proof H21. apply (Q'Abs_PrMult (φ3[t]) a) in H25; auto.
  rewrite <-H20 in H25.
  assert (Q'0 < |b|).
  { pose proof H22. apply (Q'0_le_Q'Abs b) in H26 as [_[]]; auto.
    apply (eq_Q'0_Q'Abs b) in H26; auto. elim H23; auto. }
  assert (Q'0 < |a|).
  { pose proof H21. apply (Q'0_le_Q'Abs a) in H27 as [_[]]; auto.
    apply (eq_Q'0_Q'Abs a) in H27; auto. rewrite H27,
    Q'_Mult_Property1 in H20; auto. elim H23; auto. }
  pose proof H15. apply mt_Q'0_Q'Abs in H15; auto.
  rewrite H15 in H25.
  assert (|b| ∈ Q' /\ |a| ∈ Q') as [].
  { split; apply Q'Abs_in_Q'; auto. }
  pose proof H29. apply (Q'_Ord_Tri _ (φ3[t])) in H31 as [H31|]; auto.
  - replace (φ3[t]) with (φ3[t] · Q'1) in H31.
    rewrite H25 in H31. apply Q'_Mult_PrOrder in H31; auto with Q'.
    assert (|a| ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split. rewrite Q'_N_equ_Q'_Z_me_Q'0; auto.
      apply AxiomII; repeat split; eauto. pose proof H21.
      apply (Q'_Ord_Tri Q'0) in H32 as [H32|[|]]; auto with Q'.
      - apply mt_Q'0_Q'Abs in H32; auto. rewrite H32; auto.
      - apply lt_Q'0_Q'Abs in H32; auto. rewrite H32.
        apply Q'_Z_Minus_in_Q'_Z; auto. apply Q'0_in_Q'_Z; auto.
      - symmetry in H32. apply eq_Q'0_Q'Abs in H32; auto.
        rewrite H32. apply Q'0_in_Q'_Z; auto.
      - apply AxiomII; split; eauto. intro. apply MKT41 in H32;
        eauto with Q'. apply (eq_Q'0_Q'Abs a) in H32; auto. }
    apply Q'_Q_propersubset_Q'_Arch_Lemma in H32 as []; auto.
    rewrite H32 in H31. elim (Q'_Ord_irReflex (|a|) (|a|)); auto.
    apply (Q'_Ord_Trans _ _ Q'1) in H32; auto with Q'.
    elim (Q'_Ord_irReflex Q'1 Q'1); auto with Q'.
    apply Q'_Mult_Property2; auto.
  - assert (|b| ∈ Q'_N).
    { rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; repeat split; eauto.
      pose proof H22. apply MKT4' in H19 as [H19 _].
      apply (Q'_Ord_Tri Q'0) in H32 as [H32|[|]]; auto with Q'.
      - apply mt_Q'0_Q'Abs in H32; auto. rewrite H32; auto.
      - apply lt_Q'0_Q'Abs in H32; auto. rewrite H32.
        apply Q'_Z_Minus_in_Q'_Z; auto. apply Q'0_in_Q'_Z; auto.
      - symmetry in H32. apply eq_Q'0_Q'Abs in H32; auto.
        rewrite H32. apply Q'0_in_Q'_Z; auto. }
    destruct φ1_is_Function as [[][]]. destruct φ2_is_Function as [[][]].
    destruct φ4_is_Function as [[][]]. destruct φ_is_Function as [[][]].
    unfold Q'_N in H32. rewrite reqdi in H32. apply Property_Value in H32; auto.
    apply AxiomII' in H32 as [_]. apply AxiomII' in H32 as [_[y[]]].
    apply AxiomII' in H32 as [_[y1[]]].
    assert ([(|b|),y1] ∈ φ3⁻¹).
    { apply AxiomII'; split. apply MKT49a; eauto. apply (@ MKT49c1 y1 y); eauto.
      apply AxiomII'; split; eauto. apply MKT49a; eauto.
      assert (Ensemble ([y1,y])); eauto. apply MKT49b in H51; tauto. }
    apply Property_ran in H32. rewrite H48 in H32. pose proof H51.
    apply Property_dom in H51. rewrite <-reqdi in H51.
    apply Property_Fun in H52; auto. pose proof H32.
    apply AxiomII in H53 as [_[n[]]].
    assert ((F n) ∈ N'_N). { apply Fn_in_N'_N; auto. }
    apply (N'_Infty t (F n)) in H55; auto. apply φ3_PrOrder in H55; auto.
    rewrite <-H54,H52,f11vi in H55; auto. destruct H31.
    apply (Q'_Ord_Trans _ _ (|b|)) in H55; auto.
    elim (Q'_Ord_irReflex (|b|) (|b|)); auto. rewrite <-H31 in H55.
    elim (Q'_Ord_irReflex (|b|) (|b|)); auto. rewrite <-H54; auto.
Qed.

(* *Q_Arch 是 *Q 的真子集. *)
Property Q'_Arch_propersubset_Q' : Q'_Arch ⊂ Q' /\ Q'_Arch <> Q'.
Proof.
  split. apply Q'_Arch_subset_Q'. destruct NPAUF. intro.
  assert (∃ t, t ∈ (N' ~ N'_N)) as [t].
  { assert (N'_N ⊂ N' /\ N'_N <> N') as []. { apply N'_N_propersubset_N'; auto. }
    assert ((N' ~ N'_N) <> 0).
    { intro. elim H3. apply AxiomI; split; intros.
      apply H2; auto. apply NNPP; intro.
      assert (z ∈ 0).
      { rewrite <-H4. apply MKT4'; split; auto. apply AxiomII; split; eauto. }
      elim (@ MKT16 z); auto. }
    apply NEexE in H4; auto. }
  assert (∀ n, n ∈ ω -> (F n) < t)%n'.
  { intros. apply N'_Infty,Fn_in_N'_N; auto. }
  assert (∀ n, n ∈ ω -> φ2[φ1[F n]] < φ2[φ1[t]]).
  { intros. destruct φ1_is_Function as [[][]]. destruct φ2_is_Function as [[][]].
    assert (t ∈ N' /\ (F n) ∈ N') as [].
    { apply MKT4' in H2 as []. split; auto. apply Fn_in_N'; destruct H; auto. }
    apply H3,φ1_PrOrder in H4; auto. rewrite <-H7 in H13,H14.
    apply Property_Value,Property_ran in H13; auto.
    apply Property_Value,Property_ran in H14; auto.
    rewrite H8 in H13,H14. destruct Z'_N'_propersubset_Z'.
    apply H15 in H13; apply H15 in H14. apply φ2_PrOrder in H4; auto. }
  assert ((φ2[φ1[t]]) ∈ Q').
  { apply MKT4' in H2 as []. destruct φ1_is_Function as [[][]].
    destruct φ2_is_Function as [[][]]. rewrite <-H8 in H2.
    apply Property_Value,Property_ran in H2; auto. rewrite H9 in H2.
    destruct Z'_N'_propersubset_Z' as []. apply H14 in H2. rewrite <-H12 in H2.
    apply Property_Value,Property_ran in H2; auto. rewrite H13 in H2.
    destruct Q'_Z'_propersubset_Q'. apply H16; auto. }
  rewrite <-H1 in H5. apply AxiomII in H5 as [H5[H6[k[]]]].
  assert (∃ m, m ∈ ω /\ k = φ2[φ1[F m]]) as [m[]].
  { destruct φ4_is_Function as [[][]]. assert (k ∈ ran(φ4)); auto.
    rewrite reqdi in H13. apply Property_Value,Property_ran in H13; auto.
    rewrite <-deqri,H11 in H13. exists ((φ4⁻¹)[k]). split; auto.
    destruct φ_is_Function as [[][]]. rewrite <-H16 in H13.
    apply Property_Value in H13; auto. apply AxiomII' in H13 as [H13[]].
    rewrite <-H19. destruct φ1_is_Function as [[][]].
    destruct φ1_is_Function as [[][]]. rewrite φ4_Lemma,f11vi; auto. }
  apply H4 in H9. rewrite <-H10 in H9. pose proof H6.
  apply (Self_le_Q'Abs (φ2[φ1[t]])) in H11; auto.
  assert (k < |(φ2[φ1[t]])|).
  { destruct H11. rewrite <-H11; auto. apply (Q'_Ord_Trans k) in H11; auto.
    apply φ4_is_Function in H7; auto. apply Q'Abs_in_Q'; auto. }
  apply φ4_is_Function in H7; auto. destruct H8.
  - rewrite H8 in H12. elim (Q'_Ord_irReflex k k); auto.
  - apply (Q'_Ord_Trans k) in H8; auto.
    elim (Q'_Ord_irReflex k k); auto. apply Q'Abs_in_Q'; auto.
Qed.

(* 任何*Q_Arch中的元素 小于 *Q ~ *Q_Arch 中元素的绝对值. *)
Property Q'_Arch_lt_Q'_Infty_Abs : ∀ t, t ∈ Q'
  -> t ∈ (Q' ~ Q'_Arch) <-> (∀ u, u ∈ Q'_Arch -> u < |t|).
Proof.
  destruct NPAUF. split; intros.
  - apply MKT4' in H2 as []. apply AxiomII in H4 as [].
    apply AxiomII in H3 as [H3[H6[x[]]]].
    assert (|t| ∈ Q'). { apply Q'Abs_in_Q'; auto. }
    assert (u ∈ Q' /\ |t| ∈ Q') as []; auto.
    apply (Q'_Ord_Tri _ (|t|)) in H10 as []; auto; clear H11. elim H5.
    apply AxiomII; repeat split; auto. exists x. split; auto. pose proof H6.
    apply (Self_le_Q'Abs u) in H11; auto. destruct H11.
    + rewrite <-H11 in H8. destruct H8. rewrite H8 in H10.
      destruct H10; auto. destruct H10.
      apply (Q'_Ord_Trans _ _ x) in H10; auto.
      apply φ4_is_Function; auto. rewrite H10 in H8; auto.
    + assert (|t| < |u|).
      { destruct H10. apply (Q'_Ord_Trans _ u _); auto.
        apply Q'Abs_in_Q'; auto. rewrite <-H10; auto. }
      destruct H8. rewrite H8 in H12; auto.
      apply (Q'_Ord_Trans _ _ x) in H12; auto.
      apply Q'Abs_in_Q'; auto. apply φ4_is_Function; auto.
  - apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply AxiomII in H3 as [H3[H4[x[]]]].
    pose proof H5. apply Q'_N_subset_Q' in H5; auto.
    assert (x ∈ Q'_Arch).
    { apply AxiomII; repeat split; eauto. exists x.
      split; auto. rewrite Q'_N_equ_Q'_Z_me_Q'0 in H7; auto.
      apply AxiomII in H7 as [_[_[]]]. symmetry in H7.
      pose proof H7. apply eq_Q'0_Q'Abs in H7; auto.
      rewrite H7; auto. apply mt_Q'0_Q'Abs in H7; auto. }
    apply H2 in H8. destruct H6.
    + rewrite H6 in H8. elim (Q'_Ord_irReflex x x); auto.
    + apply (Q'_Ord_Trans _ _ x) in H8; auto.
      elim (Q'_Ord_irReflex x x); auto. apply Q'Abs_in_Q'; auto.
Qed.

(* '无穷'加'有限'还是'无穷'*)
Property infinity_Plus_finity : ∀ u v, u ∈ (Q' ~ Q'_Arch)
  -> v ∈ Q'_Arch -> (u + v) ∈ (Q' ~ Q'_Arch).
Proof.
  destruct NPAUF. intros. assert (u ∈ Q' /\ v ∈ Q') as [].
  { apply MKT4' in H1 as []. apply Q'_Arch_subset_Q' in H2; auto. }
  pose proof H3. apply Q'_Arch_lt_Q'_Infty_Abs in H5 as []; auto.
  clear H6. assert (Q'0 ∈ Q' /\ u ∈ Q') as []. { split; auto with Q'. }
  apply (Q'_Ord_Tri _ u) in H6; auto; clear H7.
  assert (Q'0 ∈ Q' /\ v ∈ Q') as []. { split; auto with Q'. }
  apply (Q'_Ord_Tri _ v) in H7; auto; clear H8.
  assert (Q'0 <> u).
  { intro. apply MKT4' in H1 as []. apply AxiomII in H9 as []; eauto.
    elim H10. rewrite <-H8. apply Q'0_in_Q'_Arch; auto. }
  destruct (classic (Q'0 = v)). rewrite <-H9,Q'_Plus_Property; auto.
  apply Q'_Arch_lt_Q'_Infty_Abs; auto with Q'. intros.
  assert (u0 ∈ Q'). { apply Q'_Arch_subset_Q'; auto. }
  destruct H6 as [H6|[]]; destruct H7 as [H7|[]]; try contradiction.
  - assert (Q'0 < (u + v)).
    { apply (Q'_Plus_PrOrder _ _ u) in H7; auto with Q'.
      rewrite Q'_Plus_Property in H7; auto.
      apply (Q'_Ord_Trans _ u); auto with Q'. }
    apply mt_Q'0_Q'Abs in H6;
    apply mt_Q'0_Q'Abs in H7;
    apply mt_Q'0_Q'Abs in H12; auto with Q'. rewrite H12.
    assert ((u0 - v) ∈ Q'_Arch).
    { apply Q'_Arch_Minus_in_Q'_Arch; auto. }
    apply H5 in H13; auto. rewrite H6 in H13.
    apply (Q'_Plus_PrOrder _ _ v) in H13; auto with Q'.
    rewrite Q'_Plus_Commutation; auto.
    replace u0 with (v + (u0 - v)); auto.
    apply Q'_Minus_Plus; auto with Q'.
  - pose proof H6. apply mt_Q'0_Q'Abs in H12; auto.
    pose proof H7. apply lt_Q'0_Q'Abs in H13; auto.
    pose proof H7. apply Q'_Plus_PrOrder_Corollary in H14
    as [v1[[H14[]]]]; auto with Q'. clear H17.
    assert (Q'0 - v = v1).
    { apply Q'_Minus_Plus; auto with Q'. } rewrite H17 in H13.
    assert (v1 ∈ Q'_Arch).
    { rewrite <-H17. apply Q'_Arch_Minus_in_Q'_Arch; auto with Q'. }
    assert (Q'0 < (u + v)).
    { rewrite <-H16,(Q'_Plus_Commutation u); auto.
      apply Q'_Plus_PrOrder; auto. rewrite <-H12. apply H5; auto. }
    apply mt_Q'0_Q'Abs in H19; auto with Q'. rewrite H19.
    assert ((v1 + u0) ∈ Q'_Arch). auto with Q'.
    apply H5 in H20; auto. rewrite H12 in H20.
    apply (Q'_Plus_PrOrder _ _ v) in H20; auto with Q'.
    rewrite <-Q'_Plus_Association,H16,Q'_Plus_Commutation,
    Q'_Plus_Property,Q'_Plus_Commutation in H20; auto with Q'.
  - assert ((u + v) < Q'0).
    { apply H5 in H2; auto. apply lt_Q'0_Q'Abs in H6;
      auto. rewrite H6 in H2.
      apply (Q'_Plus_PrOrder _ _ u) in H2; auto with Q'.
      rewrite <-Q'_Mix_Association1,Q'_Plus_Property in H2;
      auto with Q'. replace Q'0 with (u - u); auto.
      apply Q'_Minus_Plus; auto with Q'.
      rewrite Q'_Plus_Property; auto with Q'. }
    apply lt_Q'0_Q'Abs in H12; auto with Q'. rewrite H12.
    replace (Q'0 - (u + v)) with ((Q'0 - u) - v).
    assert ((v + u0) ∈ Q'_Arch). auto with Q'.
    apply H5 in H13; auto. apply lt_Q'0_Q'Abs in H6; auto.
    rewrite H6 in H13. apply (Q'_Plus_PrOrder _ _ v); auto with Q'.
    replace (v + ((Q'0 - u) - v)) with (Q'0 - u); auto.
    + symmetry. apply Q'_Minus_Plus; auto with Q'.
    + symmetry. apply Q'_Minus_Plus; auto with Q'.
      rewrite <-Q'_Mix_Association1,<-Q'_Mix_Association1,
      Q'_Plus_Property,Q'_Plus_Commutation,Q'_Mix_Association1,
      Q'_Minus_Property1,Q'_Plus_Property; auto with Q'.
      apply Q'_Minus_Property1; auto.
  - assert ((u + v) < Q'0).
    { apply (Q'_Plus_PrOrder _ _ u) in H7; auto with Q'.
      rewrite Q'_Plus_Property in H7; auto.
      apply (Q'_Ord_Trans _ u); auto with Q'. }
    apply lt_Q'0_Q'Abs in H12; auto with Q'.
    assert ((v + u0) ∈ Q'_Arch). { auto with Q'. }
    apply H5 in H13; auto. apply (Q'_Plus_PrOrder _ _ v); auto with Q'.
    rewrite H12. replace (v + (Q'0 - (u + v))) with (|u|); auto. symmetry.
    apply Q'_Minus_Plus; auto with Q'. symmetry.
    apply Q'_Minus_Plus; auto with Q'.
    rewrite <-Q'_Mix_Association1,Q'_Plus_Association,
    (Q'_Plus_Commutation v),<-Q'_Plus_Association,
    Q'_Mix_Association1,Q'_Minus_Property1,Q'_Plus_Property; auto with Q'.
    apply Q'_Minus_Plus; auto with Q'. apply lt_Q'0_Q'Abs in H6; auto.
Qed.

(* 推论: 两个数相加为无穷, 则其中必有一个无穷数 *)
Corollary infinity_Plus_finity_Corollary : ∀ u v, u ∈ Q' -> v ∈ Q'
  -> (u + v) ∈ (Q' ~ Q'_Arch) -> u ∈ (Q' ~ Q'_Arch) \/ v ∈ (Q' ~ Q'_Arch).
Proof.
  intros. apply NNPP; intro. apply notandor in H2 as [].
  assert (u ∈ Q'_Arch).
  { apply NNPP; intro. elim H2. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. }
  assert (v ∈ Q'_Arch).
  { apply NNPP; intro. elim H3. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. }
  apply MKT4' in H1 as []. apply AxiomII in H6 as [].
  elim H7. auto with Q'.
Qed.

(* 无穷乘无穷还是无穷 *)
Property infinity_Mult_infinity : ∀ u v, u ∈ (Q' ~ Q'_Arch) -> v ∈ (Q' ~ Q'_Arch)
  -> (u · v) ∈ (Q' ~ Q'_Arch).
Proof.
  intros. pose proof H; pose proof H0.
  apply MKT4' in H1 as [H1 _]. apply MKT4' in H2 as [H2 _].
  apply Q'_Arch_lt_Q'_Infty_Abs; auto with Q'. intros.
  pose proof H3. apply Q'_Arch_subset_Q' in H3; auto.
  apply (Q'_Arch_lt_Q'_Infty_Abs u) in H4; auto.
  pose proof Q'1_in_Q'_Arch. apply (Q'_Arch_lt_Q'_Infty_Abs v) in H5; auto.
  apply (Q'_Mult_PrOrder _ _ (|u|)) in H5; auto with Q'.
  rewrite Q'_Mult_Property2,<-Q'Abs_PrMult in H5; auto with Q'.
  apply (Q'_Ord_Trans u0) in H5; auto with Q'. pose proof Q'0_in_Q'_Arch.
  apply (Q'_Arch_lt_Q'_Infty_Abs u) in H7; auto.
Qed.

(* 推论: 两个数相乘为无穷, 则其中必有一个无穷数 *)
Corollary infinity_Mult_finity_Corollary : ∀ u v, u ∈ Q' -> v ∈ Q'
  -> (u · v) ∈ (Q' ~ Q'_Arch) -> u ∈ (Q' ~ Q'_Arch) \/ v ∈ (Q' ~ Q'_Arch).
Proof.
  intros. apply NNPP; intro. apply notandor in H2 as [].
  assert (u ∈ Q'_Arch).
  { apply NNPP; intro. elim H2. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. }
  assert (v ∈ Q'_Arch).
  { apply NNPP; intro. elim H3. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. }
  apply MKT4' in H1 as []. apply AxiomII in H6 as [].
  elim H7. auto with Q'.
Qed.

(* 于是*Q中的元素有如下的大致形象:

                 ------- ···  ---------- 0 ----------  ··· -------
                 (无穷数)    (         *Q_Arch         )    (无穷数)

*)

(* 定义 无穷小集I 其中所有元素u满足: |u| < 1/k, 其中k为任意非零自然数. *)
Definition I := \{ λ u, u ∈ Q' /\ (∀ k, k ∈ (Q'_N ~ [Q'0]) -> |u| < (Q'1 / k)) \}.

Property I_subset_Q' : I ⊂ Q'.
Proof. unfold Included; intros. apply AxiomII in H; tauto. Qed.

Property I_is_Set : Ensemble I.
Proof. apply (MKT33 Q'); [apply Q'_is_Set|apply I_subset_Q']; auto. Qed.

(* I 是 *Q_Arch 的真子集 *)
Property I_propersubset_Q'_Arch : I ⊂ Q'_Arch /\ I <> Q'_Arch.
Proof.
  assert (Q'1 ∈ (Q'_N ~ [Q'0])).
  { pose proof in_ω_1. destruct φ4_is_Function as [[][]]. rewrite <-H2 in H.
    apply Property_Value,Property_ran in H; auto. rewrite φ4_1 in H; auto.
    apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
    apply MKT41 in H4; eauto with Q'. elim Q'0_isnot_Q'1; auto. }
  pose proof H. apply MKT4' in H as []. split.
  - unfold Included; intros. apply AxiomII in H2 as [H2[]].
    apply AxiomII; repeat split; auto. exists Q'1. split; auto.
    apply H4 in H0. apply (Q'_Mult_PrOrder _ _ Q'1) in H0; auto with Q'.
    rewrite Q'_Divide_Property2,Q'_Mult_Commutation,
    Q'_Mult_Property2,Q'_Mult_Property2 in H0; auto with Q'.
    rewrite Q'_Divide_Property2; auto with Q'.
  - intro. assert (Q'0 < Q'1).
    { apply Q'_N_Q'0_is_FirstMember in H0; auto. }
     assert (Q'1 ∈ Q'_Arch).
    { pose proof H. apply Q'_N_subset_Q' in H4; auto.
      apply AxiomII; repeat split; eauto. exists Q'1.
      split; auto. apply mt_Q'0_Q'Abs in H3; auto. }
    rewrite <-H2 in H4. apply AxiomII in H4 as [H4[]].
    apply H6 in H0. rewrite (mt_Q'0_Q'Abs Q'1),
    Q'_Divide_Property2 in H0; auto with Q'.
    elim (Q'_Ord_irReflex Q'1 Q'1); auto.
Qed.

Property Q'0_in_I : Q'0 ∈ I.
Proof.
  apply AxiomII; repeat split; eauto with Q'. intros. replace (|Q'0|) with Q'0.
  assert (k <> Q'0).
  { intro. apply MKT4' in H as []. apply AxiomII in H1 as [].
    elim H2. apply MKT41; eauto with Q'. }
  pose proof H. apply MKT4' in H1 as [H1 _]. apply Q'_N_subset_Q' in H1; auto.
  apply Q'_N_Q'0_is_FirstMember in H; auto.
  apply (Q'_Mult_PrOrder _ _ k); auto with Q'.
  rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto with Q'.
  symmetry. apply eq_Q'0_Q'Abs; auto with Q'.
Qed.

Global Hint Resolve Q'0_in_I : Q'.

(* [Q'0]真包含于I. 也即I中有除了Q'0之外的其他无穷小. *)
Property Q'0_Singleton_propersubset_I : [Q'0] ⊂ I /\ [Q'0] <> I.
Proof.
  destruct NPAUF. split. unfold Included; intros.
  apply MKT41 in H1; try rewrite H1; eauto with Q'. intro.
  assert (Q' ~ Q'_Arch <> 0).
  { intro. destruct Q'_Arch_propersubset_Q'. elim H4.
    apply AxiomI; split; intros; auto. apply NNPP; intro. elim (@ MKT16 z).
    rewrite <-H2. apply MKT4'; split; auto. apply AxiomII; split; eauto. }
  apply NEexE in H2 as [t]. pose proof H2. apply MKT4' in H3 as [H3 _].
  assert (t <> Q'0).
  { intro. apply MKT4' in H2 as []. apply AxiomII in H5 as [].
    elim H6. rewrite H4; eauto with Q'. }
  pose proof H3. apply Q'_Inv in H5 as [t1[[H5[]]_]]; auto.
  assert (t1 ∈ I).
  { apply AxiomII; repeat split; eauto. intros.
    pose proof H3. apply Q'0_le_Q'Abs in H9 as [_[]]; auto.
    apply (eq_Q'0_Q'Abs t) in H9; auto. elim H4; auto.
    assert (k <> Q'0).
    { intro. apply MKT4' in H8 as [_]. apply AxiomII in H8 as [].
      elim H11. apply MKT41; eauto with Q'. }
    pose proof H8. apply MKT4' in H11 as [H11 _].
    pose proof H11. apply Q'_N_subset_Q' in H11; auto.
    apply Q'_N_Q'0_is_FirstMember in H8; auto.
    apply (Q'_Mult_PrOrder _ _ (|t|)); auto with Q'.
    rewrite <-Q'Abs_PrMult,H7,(mt_Q'0_Q'Abs Q'1); auto with Q'.
    apply (Q'_Mult_PrOrder _ _ k); auto with Q'.
    rewrite Q'_Mult_Property2,<-Q'_Mult_Association,
    (Q'_Mult_Commutation k),Q'_Mult_Association,
    Q'_Divide_Property3,Q'_Mult_Property2; auto with Q'.
    apply Q'_Arch_lt_Q'_Infty_Abs; auto.
    apply Q'_N_propersubset_Q'_Arch; auto. }
  rewrite <-H1 in H8. apply MKT41 in H8; eauto with Q'.
Qed.

(* I对加法封闭 *)
Property I_Plus_in_I : ∀ u v, u ∈ I -> v ∈ I -> (u + v) ∈ I.
Proof.
  intros. apply AxiomII in H as [H[]]. apply AxiomII in H0 as [H0[]].
  apply AxiomII. pose proof Q'0_in_Q'.
  assert ((u + v) ∈ Q'). { apply Q'_Plus_in_Q'; auto. }
  repeat split; eauto. intros. assert ((k + k) ∈ (Q'_N ~ [Q'0])).
  { pose proof H7. apply Q'_N_Q'0_is_FirstMember in H7; auto.
    apply MKT4' in H8 as [H8 _]. apply MKT4'; split.
    apply Q'_N_Plus_in_Q'_N; auto. apply Q'_N_subset_Q' in H8; auto.
    apply AxiomII; split; eauto with Q'. intro. apply MKT41 in H9; eauto.
    pose proof H7. apply (Q'_Plus_PrOrder _ _ k) in H7; auto.
    rewrite Q'_Plus_Property in H7; auto.
    apply (Q'_Ord_Trans Q'0) in H7; auto with Q'. rewrite H9 in H7.
    elim (Q'_Ord_irReflex Q'0 Q'0); auto. }
  pose proof H8. apply H2 in H8; apply H4 in H9. pose proof Q'1_in_Q'.
  assert (k ∈ Q').
  { apply MKT4' in H7 as []. apply Q'_N_subset_Q' in H7; auto. }
  apply Q'_N_Q'0_is_FirstMember in H7; auto.
  assert (k <> Q'0).
  { intro. rewrite H12 in H7. elim (Q'_Ord_irReflex Q'0 Q'0); auto. }
  assert (Q'0 < (k + k)).
  { pose proof H7. apply (Q'_Plus_PrOrder _ _ k) in H13; auto.
    rewrite Q'_Plus_Property in H13; auto.
    apply (Q'_Ord_Trans Q'0) in H13; auto with Q'. }
  assert ((k + k) <> Q'0).
  { intro. rewrite H14 in H13. elim (Q'_Ord_irReflex Q'0 Q'0); auto. }
  assert ((|u| + |v|) < ((Q'1 / (k + k)) + (Q'1 / (k + k)))).
  { apply (Q'_Plus_PrOrder _ _ (|u|)) in H9; auto with Q'.
    apply (Q'_Ord_Trans _ (|u| + (Q'1 / (k + k)))); auto with Q'.
    rewrite Q'_Plus_Commutation; auto with Q'.
    apply Q'_Plus_PrOrder; auto with Q'. }
  replace (Q'1 / k) with ((Q'1 / (k + k)) + (Q'1 / (k + k))).
  - pose proof H1. apply (Q'Abs_inEqu u v) in H16 as []; auto.
    rewrite H16; auto. apply (Q'_Ord_Trans _ (|u| + |v|)); auto with Q'.
  - apply (Q'_Mult_Cancellation (k + k)); auto with Q'.
    rewrite Q'_Mult_Distribution,Q'_Divide_Property3,
    Q'_Mult_Commutation,Q'_Mult_Distribution,Q'_Mult_Commutation,
    Q'_Divide_Property3; auto with Q'.
Qed.

Global Hint Resolve I_Plus_in_I : Q'.

(* I对乘法封闭 (无穷小乘有限即为无穷小) *)
Property I_Mult_in_I : ∀ u v, u ∈ I -> v ∈ Q'_Arch -> (u · v) ∈ I.
Proof.
  intros. apply AxiomII in H as [H[]]. apply AxiomII in H0 as [H0[H3[k[]]]].
  apply AxiomII; repeat split; eauto with Q'. intros.
  assert (k ∈ Q' /\ k0 ∈ Q') as [].
  { apply MKT4' in H6 as []. split; apply Q'_N_subset_Q'; auto. }
  assert (k0 <> Q'0).
  { intro. apply MKT4' in H6 as []. apply AxiomII in H10 as [].
    elim H11. apply MKT41; eauto with Q'. }
  destruct (classic (k = Q'0)).
  - assert (|v| = Q'0).
    { rewrite H10 in H5. destruct H5; auto. pose proof H3.
      apply Q'0_le_Q'Abs in H11 as [_[]]; auto.
      apply (Q'_Ord_Trans _ _ Q'0) in H11; auto with Q'.
      elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
    rewrite Q'Abs_PrMult,H11,Q'_Mult_Property1; auto with Q'.
    apply Q'_N_Q'0_is_FirstMember in H6; auto.
    apply (Q'_Mult_PrOrder _ _ k0); auto with Q'.
    rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto with Q'.
  - assert ((k · k0) ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split. apply MKT4' in H6 as [].
      apply Q'_N_Mult_in_Q'_N; auto. apply AxiomII; split; eauto with Q'.
      intro. apply MKT41 in H11; eauto with Q'.
      apply Q'_Mult_Property3 in H11 as []; auto. }
    assert ((k · k0) <> Q'0).
    { intro. apply MKT4' in H11 as [_]. apply AxiomII in H11 as [].
      elim H13. apply MKT41; eauto with Q'. }
    pose proof H11. apply H2 in H11.
    apply Q'_N_Q'0_is_FirstMember in H6,H13; auto.
    rewrite (Q'Abs_PrMult u v); auto.
    apply (Q'_Mult_PrOrder _ _ (k · k0)) in H11; auto with Q'.
    rewrite Q'_Divide_Property3 in H11; auto with Q'.
    apply (Q'_Mult_PrOrder _ _ k0); auto with Q'.
    rewrite Q'_Divide_Property3; auto with Q'. destruct H5.
    + rewrite H5,(Q'_Mult_Commutation _ k),<-Q'_Mult_Association,
      (Q'_Mult_Commutation k0); auto with Q'.
    + pose proof H3. apply Q'0_le_Q'Abs in H14 as [_[]]; auto.
      rewrite H14,Q'_Mult_Property1,Q'_Mult_Property1; auto with Q'.
      pose proof H11. apply (Q'_Mult_PrOrder _ _ |v|) in H11; auto with Q'.
      rewrite Q'_Mult_Property2 in H11; auto with Q'.
      apply (Q'_Ord_Trans _ _ k) in H11; auto with Q'.
      apply (Q'_Ord_Trans _ _ k) in H14; auto with Q'.
      apply (Q'_Mult_PrOrder _ _ k); auto with Q'. rewrite
      <-Q'_Mult_Association,(Q'_Mult_Commutation (|u|)),
      <-Q'_Mult_Association,(Q'_Mult_Commutation _ |v|),
      Q'_Mult_Association,Q'_Mult_Property2; auto with Q'.
Qed.

Global Hint Resolve I_Mult_in_I : Q'.

(* 乘法封闭性的推论(相乘为无穷小, 其中必有一个为无穷小) *)
Corollary I_Mult_in_I_Corollary : ∀ u v, u ∈ Q' -> v ∈ Q' -> (u · v) ∈ I
  -> u ∈ I \/ v ∈ I.
Proof.
  intros. apply NNPP; intro. apply notandor in H2 as [].
  apply AxiomII in H1 as [H1[]].
  assert (∃ m, m ∈ (Q'_N ~ [Q'0]) /\ ~ |u| < (Q'1 / m)) as [m[]].
  { apply NNPP; intros. intro. elim H2. apply AxiomII; repeat split; eauto.
    intros. apply NNPP; intro. elim H6. exists k. auto. }
  assert (∃ m, m ∈ (Q'_N ~ [Q'0]) /\ ~ |v| < (Q'1 / m)) as [n[]].
  { apply NNPP; intros. intro. elim H3. apply AxiomII; repeat split; eauto.
    intros. apply NNPP; intro. elim H8. exists k. auto. }
  assert (m ∈ Q' /\ n ∈ Q') as [].
  { apply MKT4' in H6 as []; apply MKT4' in H8 as [].
    split; apply Q'_N_subset_Q'; auto. }
  pose proof Q'0_in_Q'. pose proof Q'1_in_Q'.
  assert (m <> Q'0 /\ n <> Q'0) as [].
  { apply MKT4' in H6 as [_], H8 as [_].
    apply AxiomII in H6 as [_], H8 as [_].
    split; intro; [elim H6|elim H8]; apply MKT41; eauto with Q'. }
  assert ((m · n) ∈ (Q'_N ~ [Q'0]) /\ Q'0 < m /\ Q'0 < n) as [H16[]].
  { split; [ |apply Q'_N_Q'0_is_FirstMember in H6,H8]; auto.
    apply MKT4'; split. apply MKT4' in H6 as [], H8 as [].
    apply Q'_N_Mult_in_Q'_N; auto. apply AxiomII; split; eauto with Q'. intro.
    apply MKT41 in H16; eauto with Q'. apply Q'_Mult_Property3 in H16 as []; auto. }
  assert ((Q'1 / m) < |u| \/ (Q'1 / m) = |u|).
  { destruct (Q'_Ord_Tri (Q'1 / m) (|u|)) as [H19|[]]; auto with Q'.
    elim H7; auto. }
  assert ((Q'1 / n) < |v| \/ (Q'1 / n) = |v|).
  { destruct (Q'_Ord_Tri (Q'1 / n) |v|) as [H20|[]]; auto with Q'.
    elim H9; auto. }
  assert (Q'0 < |u|).
  { pose proof H. apply (Q'0_le_Q'Abs u) in H21 as [H21[]]; auto.
    apply (eq_Q'0_Q'Abs u) in H22; auto. elim H2. rewrite H22.
    apply Q'0_in_I; auto. }
  assert (Q'0 < |v|).
  { pose proof H0. apply (Q'0_le_Q'Abs v) in H22 as [H22[]]; auto.
    apply (eq_Q'0_Q'Abs v) in H23; auto. elim H3. rewrite H23.
    apply Q'0_in_I; auto. }
  assert ((m · n) <> Q'0).
  { intro. apply MKT4' in H16 as []. apply AxiomII in H24 as [].
    elim H25. apply MKT41; eauto with Q'. }
  pose proof H16. apply Q'_N_Q'0_is_FirstMember in H6,H8,H16; auto.
  apply H5 in H24. apply (Q'_Mult_PrOrder _ _ (m · n)) in H24; auto with Q'.
  rewrite Q'_Divide_Property3 in H24; auto with Q'. pose proof H.
  apply (Q'Abs_PrMult u v) in H25; auto. destruct H19,H20.
  - apply (Q'_Mult_PrOrder _ _ m) in H19; auto with Q'.
    apply (Q'_Mult_PrOrder _ _ n) in H20; auto with Q'.
    rewrite Q'_Divide_Property3 in H19,H20; auto with Q'.
    apply (Q'_Mult_PrOrder _ _ (m · |u|)) in H20; auto with Q'.
    rewrite Q'_Mult_Property2 in H20; eauto with Q'.
    apply (Q'_Ord_Trans Q'1) in H20; auto with Q'.
    rewrite Q'_Mult_Association,<-(Q'_Mult_Association (|u|)),
    (Q'_Mult_Commutation _ n),<-Q'_Mult_Association,
    <-Q'_Mult_Association,Q'_Mult_Association,<-H25 in H20; auto with Q'.
    apply (Q'_Ord_Trans Q'1) in H24; auto with Q'.
    elim (Q'_Ord_irReflex Q'1 Q'1); auto.
    apply (Q'_Ord_Trans _ Q'1); auto with Q'.
  - apply (Q'_Mult_PrOrder _ _ m) in H19; auto with Q'.
    rewrite Q'_Divide_Property3 in H19; auto with Q'.
    apply (Q'_Ord_Trans _ _ (m · |u|)) in H24; auto with Q'.
    rewrite Q'_Mult_Association in H24; auto with Q'.
    apply Q'_Mult_PrOrder in H24; auto with Q'.
    rewrite H25,<-Q'_Mult_Association,(Q'_Mult_Commutation n),
    Q'_Mult_Association,<-H20,Q'_Divide_Property3,
    Q'_Mult_Property2 in H24; auto with Q'.
    elim (Q'_Ord_irReflex (|u|) (|u|)); auto with Q'.
  - apply (Q'_Mult_PrOrder _ _ n) in H20; auto with Q'.
    rewrite Q'_Divide_Property3 in H20; auto with Q'.
    apply (Q'_Ord_Trans _ _ (n · |v|)) in H24; auto with Q'.
    rewrite (Q'_Mult_Commutation m),
    Q'_Mult_Association in H24; auto with Q'.
    apply Q'_Mult_PrOrder in H24; auto with Q'.
    rewrite H25,<-Q'_Mult_Association,<-H19,Q'_Divide_Property3,
    Q'_Mult_Commutation,Q'_Mult_Property2 in H24; auto with Q'.
    elim (Q'_Ord_irReflex |v| |v|); auto with Q'.
  - apply Q'_Divide_Mult in H19,H20; auto with Q'.
    rewrite H25,Q'_Mult_Association,<-(Q'_Mult_Association n),
    (Q'_Mult_Commutation n),(Q'_Mult_Association (|u|)),
    <-(Q'_Mult_Association m),H19,H20,Q'_Mult_Property2 in H24; auto with Q'.
    elim (Q'_Ord_irReflex Q'1 Q'1); auto.
Qed.

(* I中非零元的逆元都在 *Q ~ *Q_Arch 中. 即无穷小的逆元都是无穷大. *)
Property I_Inv_Property1 : ∀ u v, u ∈ (I ~ [Q'0]) -> v ∈ Q'
  -> u · v = Q'1 -> v ∈ (Q' ~ Q'_Arch).
Proof.
  destruct NPAUF. intros. apply MKT4' in H1 as [].
  assert (u ∈ Q'). { apply I_subset_Q' in H1; auto. }
  pose proof Q'0_in_Q'. pose proof Q'1_in_Q'.
  apply MKT4'; split; auto. apply AxiomII; split; eauto.
  intro. apply AxiomII in H8 as [H8[H9[x[]]]]. apply AxiomII in H1 as [H1[]].
  assert (Q'0 < Q'1).
  { rewrite Q'0_Property,Q'1_Property; auto.
    apply Q'_Ord_Instantiate; auto with Z'.
    rewrite Z'_Mult_Property2,Z'_Mult_Property2; auto with Z'. }
  apply mt_Q'0_Q'Abs in H14; auto. rewrite <-H3,Q'Abs_PrMult,H3 in H14; auto.
  assert (∀ k, k ∈ Q'_N -> k < |v|).
  { assert (Q'0 < |v|).
    { pose proof H2. apply Q'0_le_Q'Abs in H15 as [H15[]]; auto.
      rewrite H16,Q'_Mult_Property1 in H14; auto.
      elim Q'0_isnot_Q'1; auto. apply Q'Abs_in_Q'; auto. }
    assert (Q'0 < (|u|)).
    { pose proof H5. apply Q'0_le_Q'Abs in H16 as [H16[]]; auto.
      rewrite H17,Q'_Mult_Commutation,Q'_Mult_Property1 in H14;
      auto; try apply Q'Abs_in_Q'; auto. elim Q'0_isnot_Q'1; auto. }
    intros. destruct (classic (k = Q'0)). rewrite H18; auto.
    assert (k ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H19; eauto. }
    pose proof H19. apply Q'_N_Q'0_is_FirstMember in H20; auto.
    apply H13 in H19. pose proof H17. apply Q'_N_subset_Q' in H17; auto.
    apply (Q'_Mult_PrOrder _ _ (|u|)); auto with Q'.
    rewrite H14; auto. apply (Q'_Mult_PrOrder _ _ k) in H19; auto with Q'.
    rewrite Q'_Divide_Property3,Q'_Mult_Commutation in H19; auto with Q'. }
  assert (x ∈ Q'). { apply Q'_N_subset_Q' in H10; auto. }
  apply H15 in H10. destruct H11; try rewrite H11 in H10;
  try apply (Q'_Ord_Trans _ _ x) in H10; auto with Q';
  elim (Q'_Ord_irReflex x x); auto.
Qed.

(* *Q ~ *Q_Arch 中的逆元都在 I ~ [Q'0] 中. 即无穷大的逆元都是无穷小.*)
Property I_inv_Property2 : ∀ u v, u ∈ (Q' ~ Q'_Arch) -> v ∈ Q'
  -> u · v = Q'1 -> v ∈ (I ~ [Q'0]).
Proof.
  destruct NPAUF. intros. assert (u ∈ Q'). { apply MKT4' in H1; tauto. }
  pose proof Q'0_in_Q'. pose proof Q'1_in_Q'.
  assert (u <> Q'0 /\ v <> Q'0) as [].
  { split; intro; rewrite H7 in H3; try rewrite Q'_Mult_Property1 in H3;
    try rewrite Q'_Mult_Commutation,Q'_Mult_Property1 in H3; auto;
    elim Q'0_isnot_Q'1; auto. }
  assert (Q'0 < Q'1); auto with Q'. apply mt_Q'0_Q'Abs in H9; auto.
  rewrite <-H3,Q'Abs_PrMult,H3 in H9; auto. pose proof H4; pose proof H2.
  apply (Q'0_le_Q'Abs u) in H10 as [H10[]];
  apply (Q'0_le_Q'Abs v) in H11 as [H11[]]; auto;
  try rewrite H12 in H9; try rewrite H13 in H9;
  try rewrite Q'_Mult_Property1 in H9;
  try rewrite Q'_Mult_Commutation,Q'_Mult_Property1 in H9;
  auto; pose proof Q'0_isnot_Q'1; try contradiction. clear H14.
  pose proof H4. apply (Q'_Arch_lt_Q'_Infty_Abs u) in H14; auto.
  assert (∀ v, v ∈ Q'_Arch -> v < |u|). { apply H14; auto. } clear H14.
  apply MKT4'; split.
  - apply AxiomII; repeat split; eauto. intros.
    pose proof H14. apply MKT4' in H16 as [H16 _].
    assert (k ∈ Q'). { apply Q'_N_subset_Q' in H16; auto. }
    assert (k ∈ Q'_Arch).
    { apply AxiomII; repeat split; eauto. exists k. split; auto.
      apply Q'_N_Q'0_is_FirstMember,mt_Q'0_Q'Abs in H14; auto. }
    apply H15 in H18. apply (Q'_Mult_PrOrder _ _ |v|) in H18; auto.
    rewrite Q'_Mult_Commutation in H9; auto. rewrite H9 in H18; auto.
    assert (k <> Q'0).
    { apply MKT4' in H14 as []. apply AxiomII in H19 as [].
      intro. elim H20. apply MKT41; eauto. }
    apply Q'_N_Q'0_is_FirstMember in H14; auto.
    apply (Q'_Mult_PrOrder _ _ k); auto with Q'.
    rewrite Q'_Divide_Property3,Q'_Mult_Commutation; auto with Q'.
  - apply AxiomII; split; eauto; intro. apply MKT41 in H14; eauto.
Qed.

(* 至此, 可以更进一步刻画出*Q中元素的形象:

    ------- ···  ---------- ··· -- 0 -- ··· ----------  ··· -------

                                (  I  )

    (负无穷)    (                *Q_Arch                )    (正无穷)

这里的I是无穷小集, 数的延伸实际上也就是无穷大集, (非零)无穷小与无穷大之间互逆.


实际上, 目前所描绘的形象仍然不能详尽地描绘*Q中的所有元素. 注意, I实际上可以看作是0的邻域,
I中的非零元无限接近于0, 实际上对于*Q中的每个元素q都会存在这样的领域,领域中的非q元无限接近q,
这一性质是一般有理数集所不具备的, 可见*Q是一个比有理数集'更大'的集.

在目前的*Q下已经足够建立实数集了.  *)
